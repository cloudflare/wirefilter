use super::field_expr::LhsFieldExpr;
use crate::{
    execution_context::ExecutionContext,
    filter::CompiledExpr,
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

impl<'s> IndexExpr<'s> {
    pub fn uses(&self, field: Field<'s>) -> bool {
        self.lhs.uses(field)
    }

    pub fn compile_with<F: 's>(self, func: F) -> CompiledExpr<'s>
    where
        F: Fn(&LhsValue<'_>) -> bool,
    {
        let Self { lhs, indexes } = self;
        match lhs {
            LhsFieldExpr::FunctionCallExpr(call) => CompiledExpr::new(move |ctx| {
                func(indexes.iter().fold(&call.execute(ctx), |value, idx| {
                    value.get(idx).unwrap().unwrap()
                }))
            }),
            LhsFieldExpr::Field(f) => CompiledExpr::new(move |ctx| {
                func(
                    indexes
                        .iter()
                        .fold(ctx.get_field_value_unchecked(f), |value, idx| {
                            value.get(idx).unwrap().unwrap()
                        }),
                )
            }),
        }
    }

    pub fn execute(&'s self, ctx: &'s ExecutionContext<'s>) -> LhsValue<'_> {
        if self.indexes.is_empty() {
            self.lhs.execute(ctx)
        } else {
            match &self.lhs {
                LhsFieldExpr::Field(f) => self
                    .indexes
                    .iter()
                    .fold(ctx.get_field_value_unchecked(*f), |value, index| {
                        value.get(index).unwrap().unwrap()
                    })
                    .as_ref(),
                LhsFieldExpr::FunctionCallExpr(call) => self
                    .indexes
                    .iter()
                    .fold(&call.execute(ctx), |value, index| {
                        value.get(index).unwrap().unwrap()
                    })
                    .to_owned(),
            }
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
                        indexes.push(idx);
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
                        indexes.push(idx);
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
                (Type::Map(child), FieldIndex::MapKey(_)) => (*child),
                (_, _) => unreachable!(),
            }
        }
        ty.clone()
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
