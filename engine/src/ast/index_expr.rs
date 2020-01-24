use super::field_expr::LhsFieldExpr;
use crate::{
    filter::{CompiledExpr, CompiledOneExpr, CompiledValueExpr, CompiledVecExpr},
    lex::{expect, skip_space, span, Lex, LexErrorKind, LexResult, LexWith},
    scheme::{Field, FieldIndex, IndexAccessError, Scheme},
    types::{GetType, LhsValue, Type},
};
use serde::{ser::SerializeSeq, Serialize, Serializer};

#[derive(Debug, PartialEq, Eq, Clone)]
// IndexExpr is an expr that destructures an index into an LhsFieldExpr.
//
// For example, given a scheme which declares a field, http.request.headers,
// as a map of string to list of strings, then the expression
// http.request.headers["Cookie"][0] would have an LhsFieldExpr
// http.request.headers and indexes ["Cookie", 0].
pub(crate) struct IndexExpr<'s> {
    pub lhs: LhsFieldExpr<'s>,
    pub indexes: Vec<FieldIndex>,
}

macro_rules! index_access_one {
    ($indexes:ident, $first:expr, $default:ident, $func:expr) => {
        $indexes[..(if let Some(&FieldIndex::MapEach) = $indexes.last() {
            $indexes.len() - 1
        } else {
            $indexes.len()
        })]
            .iter()
            .fold($first, |value, idx| {
                value.and_then(|val| val.get(idx).unwrap())
            })
            .map_or($default, |val| $func(val))
    };
}

macro_rules! index_access_vec {
    ($indexes:ident, $first:expr, $default:ident, $func:ident) => {
        index_access_one!($indexes, $first, $default, |val: &LhsValue<'_>| {
            let mut output = Vec::new();
            for item in val.iter().unwrap() {
                output.push($func(item));
            }
            output.into_boxed_slice()
        })
    };
}

impl<'s> IndexExpr<'s> {
    pub fn uses(&self, field: Field<'s>) -> bool {
        self.lhs.uses(field)
    }

    pub fn compile_one_with<F: 's>(self, default: bool, func: F) -> CompiledOneExpr<'s>
    where
        F: Fn(&LhsValue<'_>) -> bool + Sync + Send,
    {
        let Self { lhs, indexes } = self;
        match lhs {
            LhsFieldExpr::FunctionCallExpr(call) => {
                let call = call.compile();
                CompiledOneExpr::new(move |ctx| {
                    index_access_one!(indexes, (&call.execute(ctx)).as_ref().ok(), default, func)
                })
            }
            LhsFieldExpr::Field(f) => CompiledOneExpr::new(move |ctx| {
                index_access_one!(
                    indexes,
                    Some(ctx.get_field_value_unchecked(f)),
                    default,
                    func
                )
            }),
        }
    }

    pub fn compile_vec_with<F: 's>(self, default: &'s [bool], func: F) -> CompiledVecExpr<'s>
    where
        F: Fn(&LhsValue<'_>) -> bool + Sync + Send,
    {
        let Self { lhs, indexes } = self;
        match lhs {
            LhsFieldExpr::FunctionCallExpr(call) => {
                let call = call.compile();
                CompiledVecExpr::new(move |ctx| {
                    let default = default.to_vec().into_boxed_slice();
                    index_access_vec!(indexes, (&call.execute(ctx)).as_ref().ok(), default, func)
                })
            }
            LhsFieldExpr::Field(f) => CompiledVecExpr::new(move |ctx| {
                let default = default.to_vec().into_boxed_slice();
                index_access_vec!(
                    indexes,
                    Some(ctx.get_field_value_unchecked(f)),
                    default,
                    func
                )
            }),
        }
    }

    pub fn compile_with<F: 's>(
        self,
        default_one: bool,
        default_vec: &'s [bool],
        func: F,
    ) -> CompiledExpr<'s>
    where
        F: Fn(&LhsValue<'_>) -> bool + Sync + Send,
    {
        if self.map_each_to().is_some() {
            CompiledExpr::Vec(self.compile_vec_with(default_vec, func))
        } else {
            CompiledExpr::One(self.compile_one_with(default_one, func))
        }
    }

    pub fn compile(self) -> CompiledValueExpr<'s> {
        let ty = self.get_type();
        let Self { lhs, indexes } = self;

        let last = if let Some(&FieldIndex::MapEach) = indexes.last() {
            indexes.len() - 1
        } else {
            indexes.len()
        };
        if last == 0 {
            lhs.compile()
        } else {
            match lhs {
                LhsFieldExpr::Field(f) => CompiledValueExpr::new(move |ctx| {
                    indexes[..last]
                        .iter()
                        .fold(Some(ctx.get_field_value_unchecked(f)), |value, index| {
                            value.and_then(|val| val.get(index).unwrap())
                        })
                        .map(LhsValue::as_ref)
                        .ok_or_else(|| ty.clone())
                }),
                LhsFieldExpr::FunctionCallExpr(call) => {
                    let call = call.compile();
                    CompiledValueExpr::new(move |ctx| {
                        let result = call.execute(ctx)?;
                        indexes[..last]
                            .iter()
                            .fold(Some(result), |value, index| {
                                value.and_then(|val| val.extract(index).unwrap())
                            })
                            .ok_or_else(|| ty.clone())
                    })
                }
            }
        }
    }

    pub fn map_each_to(&self) -> Option<Type> {
        let (ty, map_each) = self.indexes.iter().fold(
            (self.lhs.get_type(), false),
            |(ty, map_each), index| match (ty, index) {
                (Type::Array(idx), FieldIndex::ArrayIndex(_)) => (*idx, map_each),
                (Type::Array(idx), FieldIndex::MapEach) => (*idx, true),
                (Type::Map(child), FieldIndex::MapKey(_)) => (*child, map_each),
                (Type::Map(child), FieldIndex::MapEach) => (*child, true),
                (_, _) => unreachable!(),
            },
        );
        if map_each {
            Some(ty)
        } else {
            None
        }
    }
}

impl<'i, 's> LexWith<'i, &'s Scheme> for IndexExpr<'s> {
    fn lex_with(mut input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        let (lhs, rest) = LhsFieldExpr::lex_with(input, scheme)?;

        let mut current_type = lhs.get_type();

        let mut indexes = Vec::new();

        input = rest;

        while let Ok(rest) = expect(input, "[") {
            let rest = skip_space(rest);

            let (idx, rest) = FieldIndex::lex(rest)?;

            let mut rest = skip_space(rest);

            rest = expect(rest, "]")?;

            match &idx {
                FieldIndex::ArrayIndex(_) => match current_type {
                    Type::Array(array_type) => {
                        current_type = *array_type;
                    }
                    _ => {
                        return Err((
                            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                                index: idx,
                                actual: current_type,
                            }),
                            span(input, rest),
                        ))
                    }
                },
                FieldIndex::MapKey(_) => match current_type {
                    Type::Map(map_type) => {
                        current_type = *map_type;
                    }
                    _ => {
                        return Err((
                            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                                index: idx,
                                actual: current_type,
                            }),
                            span(input, rest),
                        ))
                    }
                },
                FieldIndex::MapEach => match current_type {
                    Type::Array(array_type) => {
                        current_type = *array_type;
                    }
                    Type::Map(map_type) => {
                        current_type = *map_type;
                    }
                    _ => {
                        return Err((
                            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                                index: idx,
                                actual: current_type,
                            }),
                            span(input, rest),
                        ))
                    }
                },
            };

            input = rest;

            if Some(&FieldIndex::MapEach) == indexes.last() {
                return Err((LexErrorKind::InvalidMapEachAccess, input));
            }

            indexes.push(idx);
        }

        Ok((IndexExpr { lhs, indexes }, input))
    }
}

impl<'s> GetType for IndexExpr<'s> {
    fn get_type(&self) -> Type {
        let mut ty = self.lhs.get_type();
        for index in &self.indexes {
            ty = match (ty, index) {
                (Type::Array(idx), FieldIndex::ArrayIndex(_)) => (*idx),
                (Type::Array(idx), FieldIndex::MapEach) => (*idx),
                (Type::Map(child), FieldIndex::MapKey(_)) => (*child),
                (Type::Map(child), FieldIndex::MapEach) => (*child),
                (_, _) => unreachable!(),
            }
        }
        ty
    }
}

impl<'s> Serialize for IndexExpr<'s> {
    fn serialize<S: Serializer>(&self, ser: S) -> Result<S::Ok, S::Error> {
        if self.indexes.is_empty() {
            self.lhs.serialize(ser)
        } else {
            let mut seq = ser.serialize_seq(Some(self.indexes.len() + 1))?;
            match &self.lhs {
                LhsFieldExpr::Field(field) => seq.serialize_element(field)?,
                LhsFieldExpr::FunctionCallExpr(call) => seq.serialize_element(call)?,
            };
            for index in &self.indexes {
                seq.serialize_element(index)?;
            }
            seq.end()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ast::field_expr::LhsFieldExpr, FieldIndex};
    use lazy_static::lazy_static;

    lazy_static! {
        static ref SCHEME: Scheme = {
            let scheme: Scheme = Scheme! {
                test: Array(Bool),
            };
            scheme
        };
    }

    #[test]
    fn test_array_indices() {
        fn run(i: i32) {
            let filter = format!("test[{}]", i);
            assert_ok!(
                IndexExpr::lex_with(&filter, &SCHEME),
                IndexExpr {
                    lhs: LhsFieldExpr::Field(SCHEME.get_field("test").unwrap()),
                    indexes: vec![FieldIndex::ArrayIndex(i as u32)],
                }
            );
        }

        run(0);
        run(1);
        run(99);
        run(999);
        run(9999);
        run(99999);
    }
}
