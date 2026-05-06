use super::ValueExpr;
use super::field_expr::IdentifierExpr;
use super::parse::FilterParser;
use super::visitor::{Visitor, VisitorMut};
use crate::compiler::Compiler;
use crate::execution_context::ExecutionContext;
use crate::filter::{CompiledExpr, CompiledOneExpr, CompiledValueExpr, CompiledVecExpr};
use crate::lex::{Lex, LexErrorKind, LexResult, LexWith, expect, skip_space, span};
use crate::lhs_types::{Array, Map, TypedArray};
use crate::scheme::{FieldIndex, IndexAccessError};
use crate::types::{GetType, IntoIter, LhsValue, Type};
use serde::ser::SerializeSeq;
use serde::{Serialize, Serializer};

const BOOL_ARRAY: TypedArray<'_, bool> = TypedArray::new();

/// IndexExpr is an expr that destructures an index into an IdentifierExpr.
///
/// For example, given a scheme which declares a field `http.request.headers`,
/// as a map of string to list of strings, then the expression
/// `http.request.headers["Cookie"][0]` would have an IdentifierExpr
/// of `http.request.headers` and indexes `["Cookie", 0]`.
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct IndexExpr {
    /// The accessed identifier.
    pub identifier: IdentifierExpr,
    /// The list of indexes access.
    pub indexes: Vec<FieldIndex>,
}

#[expect(clippy::manual_ok_err)]
#[inline]
pub fn ok_ref<T, E>(result: &Result<T, E>) -> Option<&T> {
    match result {
        Ok(x) => Some(x),
        Err(_) => None,
    }
}

impl ValueExpr for IndexExpr {
    #[inline]
    fn walk<'a, V: Visitor<'a>>(&'a self, visitor: &mut V) {
        match self.identifier {
            IdentifierExpr::Field(ref field) => visitor.visit_field(field),
            IdentifierExpr::FunctionCallExpr(ref call) => visitor.visit_function_call_expr(call),
        }
    }

    #[inline]
    fn walk_mut<'a, V: VisitorMut<'a>>(&'a mut self, visitor: &mut V) {
        match self.identifier {
            IdentifierExpr::Field(ref field) => visitor.visit_field(field),
            IdentifierExpr::FunctionCallExpr(ref mut call) => {
                visitor.visit_function_call_expr(call)
            }
        }
    }

    fn compile_with_compiler<C: Compiler>(self, compiler: &mut C) -> CompiledValueExpr<C::U> {
        let mut ty = self.get_type();
        let map_each_count = self.map_each_count();
        let Self {
            identifier,
            indexes,
        } = self;

        let last = match map_each_count {
            0 => Some(indexes.len()),
            1 if indexes.last() == Some(&FieldIndex::MapEach) => {
                ty = Type::Array(ty.into());
                Some(indexes.len() - 1)
            }
            _ => None,
        };
        if last == Some(0) {
            // Fast path
            match identifier {
                IdentifierExpr::Field(f) => CompiledValueExpr::new(move |ctx| {
                    ctx.get_field_value_unchecked(&f)
                        .map(LhsValue::as_ref)
                        .ok_or(ty)
                }),
                IdentifierExpr::FunctionCallExpr(call) => compiler.compile_function_call_expr(call),
            }
        } else if let Some(last) = last {
            // Average path
            match identifier {
                IdentifierExpr::Field(f) => CompiledValueExpr::new(move |ctx| {
                    ctx.get_field_value_unchecked(&f)
                        .and_then(|value| value.get_nested(&indexes[..last]))
                        .map(LhsValue::as_ref)
                        .ok_or(ty)
                }),
                IdentifierExpr::FunctionCallExpr(call) => {
                    let call = compiler.compile_function_call_expr(call);
                    CompiledValueExpr::new(move |ctx| {
                        call.execute(ctx)
                            .ok()
                            .and_then(|val| val.extract_nested(&indexes[..last]))
                            .ok_or(ty)
                    })
                }
            }
        } else {
            let return_type = Type::Array(ty.into());
            // Slow path
            match identifier {
                IdentifierExpr::Field(f) => CompiledValueExpr::new(move |ctx| {
                    let mut iter = MapEachIterator::from_indexes(&indexes[..]);
                    iter.reset(
                        ctx.get_field_value_unchecked(&f)
                            .map(LhsValue::as_ref)
                            .ok_or(return_type)?,
                    );
                    Ok(LhsValue::Array(Array::try_from_iter(ty, iter).unwrap()))
                }),
                IdentifierExpr::FunctionCallExpr(call) => {
                    let call = compiler.compile_function_call_expr(call);
                    CompiledValueExpr::new(move |ctx| {
                        let mut iter = MapEachIterator::from_indexes(&indexes[..]);
                        iter.reset(call.execute(ctx).map_err(|_| return_type)?);
                        Ok(LhsValue::Array(Array::try_from_iter(ty, iter).unwrap()))
                    })
                }
            }
        }
    }
}

fn simplify_indexes(mut indexes: Vec<FieldIndex>) -> Box<[FieldIndex]> {
    if Some(&FieldIndex::MapEach) == indexes.last() {
        indexes.pop();
    }
    indexes.into_boxed_slice()
}

/// Interface used to implement comparison against a value.
pub trait Compare<U>: Send + Sync + 'static {
    /// Returns true if the value matches the comparison.
    fn compare<'e>(&self, value: &LhsValue<'e>, ctx: &'e ExecutionContext<'e, U>) -> bool;
}

impl IndexExpr {
    fn compile_one_with<C: Compiler>(
        self,
        compiler: &mut C,
        default: bool,
        comp: impl Compare<C::U>,
    ) -> CompiledOneExpr<C::U> {
        let Self {
            identifier,
            indexes,
        } = self;
        let indexes = simplify_indexes(indexes);
        match identifier {
            IdentifierExpr::FunctionCallExpr(call) => {
                let call = compiler.compile_function_call_expr(call);
                if indexes.is_empty() {
                    CompiledOneExpr::new(move |ctx| {
                        call.execute(ctx).map_or(
                            default,
                            #[inline]
                            |val| comp.compare(&val, ctx),
                        )
                    })
                } else {
                    CompiledOneExpr::new(move |ctx| {
                        ok_ref(&call.execute(ctx))
                            .and_then(|val| val.get_nested(&indexes))
                            .map_or(
                                default,
                                #[inline]
                                |val| comp.compare(val, ctx),
                            )
                    })
                }
            }
            IdentifierExpr::Field(f) => {
                if indexes.is_empty() {
                    CompiledOneExpr::new(move |ctx| {
                        ctx.get_field_value_unchecked(&f)
                            .map(|value| comp.compare(value, ctx))
                            .unwrap_or(default)
                    })
                } else {
                    CompiledOneExpr::new(move |ctx| {
                        ctx.get_field_value_unchecked(&f)
                            .and_then(|value| value.get_nested(&indexes))
                            .map_or(
                                default,
                                #[inline]
                                |val| comp.compare(val, ctx),
                            )
                    })
                }
            }
        }
    }

    pub(crate) fn compile_vec_with<C: Compiler>(
        self,
        compiler: &mut C,
        comp: impl Compare<C::U>,
    ) -> CompiledVecExpr<C::U> {
        let Self {
            identifier,
            indexes,
        } = self;
        let indexes = simplify_indexes(indexes);
        match identifier {
            IdentifierExpr::FunctionCallExpr(call) => {
                let call = compiler.compile_function_call_expr(call);
                CompiledVecExpr::new(move |ctx| {
                    let comp = &comp;
                    ok_ref(&call.execute(ctx))
                        .and_then(|val| val.get_nested(&indexes))
                        .map_or(
                            BOOL_ARRAY,
                            #[inline]
                            |val: &LhsValue<'_>| {
                                TypedArray::from_iter(
                                    val.iter().unwrap().map(|item| comp.compare(item, ctx)),
                                )
                            },
                        )
                })
            }
            IdentifierExpr::Field(f) => CompiledVecExpr::new(move |ctx| {
                let comp = &comp;
                ctx.get_field_value_unchecked(&f)
                    .and_then(|value| value.get_nested(&indexes))
                    .map_or(
                        BOOL_ARRAY,
                        #[inline]
                        |val: &LhsValue<'_>| {
                            TypedArray::from_iter(
                                val.iter().unwrap().map(|item| comp.compare(item, ctx)),
                            )
                        },
                    )
            }),
        }
    }

    pub(crate) fn compile_iter_with<C: Compiler>(
        self,
        compiler: &mut C,
        comp: impl Compare<C::U>,
    ) -> CompiledVecExpr<C::U> {
        let Self {
            identifier,
            indexes,
        } = self;
        match identifier {
            IdentifierExpr::Field(f) => CompiledVecExpr::new(move |ctx| {
                let mut iter = MapEachIterator::from_indexes(&indexes[..]);
                match ctx.get_field_value_unchecked(&f) {
                    Some(value) => iter.reset(value.as_ref()),
                    None => return TypedArray::default(),
                };
                TypedArray::from_iter(iter.map(|item| comp.compare(&item, ctx)))
            }),
            IdentifierExpr::FunctionCallExpr(call) => {
                let call = compiler.compile_function_call_expr(call);
                CompiledVecExpr::new(move |ctx| {
                    let mut iter = MapEachIterator::from_indexes(&indexes[..]);
                    match call.execute(ctx) {
                        Ok(val) => {
                            iter.reset(val);
                        }
                        _ => {
                            return TypedArray::default();
                        }
                    }

                    TypedArray::from_iter(iter.map(|item| comp.compare(&item, ctx)))
                })
            }
        }
    }

    /// Compiles an [`IndexExpr`] node into a [`CompiledExpr`] (boxed closure) using the
    /// provided comparison function that returns a boolean.
    pub fn compile_with<C: Compiler>(
        self,
        compiler: &mut C,
        default: bool,
        comp: impl Compare<C::U>,
    ) -> CompiledExpr<C::U> {
        match self.map_each_count() {
            0 => CompiledExpr::One(self.compile_one_with(compiler, default, comp)),
            1 if self.indexes.last() == Some(&FieldIndex::MapEach) => {
                CompiledExpr::Vec(self.compile_vec_with(compiler, comp))
            }
            _ => CompiledExpr::Vec(self.compile_iter_with(compiler, comp)),
        }
    }

    pub(crate) fn map_each_count(&self) -> usize {
        self.indexes
            .iter()
            .filter(|&index| index == &FieldIndex::MapEach)
            .count()
    }

    /// Returns the associated identifier (field or function call).
    pub fn identifier(&self) -> &IdentifierExpr {
        &self.identifier
    }

    /// Returns the index accesses as a list of [`FieldIndex`].
    pub fn indexes(&self) -> &[FieldIndex] {
        &self.indexes
    }
}

impl<'i, 's> LexWith<'i, &FilterParser<'s>> for IndexExpr {
    fn lex_with(mut input: &'i str, parser: &FilterParser<'s>) -> LexResult<'i, Self> {
        let (identifier, rest) = IdentifierExpr::lex_with(input, parser)?;

        let mut current_type = identifier.get_type();

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
                        current_type = array_type.into();
                    }
                    _ => {
                        return Err((
                            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                                index: idx,
                                actual: current_type,
                            }),
                            span(input, rest),
                        ));
                    }
                },
                FieldIndex::MapKey(_) => match current_type {
                    Type::Map(map_type) => {
                        current_type = map_type.into();
                    }
                    _ => {
                        return Err((
                            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                                index: idx,
                                actual: current_type,
                            }),
                            span(input, rest),
                        ));
                    }
                },
                FieldIndex::MapEach => match current_type {
                    Type::Array(array_type) => {
                        current_type = array_type.into();
                    }
                    Type::Map(map_type) => {
                        current_type = map_type.into();
                    }
                    _ => {
                        return Err((
                            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                                index: idx,
                                actual: current_type,
                            }),
                            span(input, rest),
                        ));
                    }
                },
            };

            input = rest;

            indexes.push(idx);
        }

        Ok((
            IndexExpr {
                identifier,
                indexes,
            },
            input,
        ))
    }
}

impl GetType for IndexExpr {
    fn get_type(&self) -> Type {
        let mut ty = self.identifier.get_type();
        for index in &self.indexes {
            ty = match (ty, index) {
                (Type::Array(sub_ty), FieldIndex::ArrayIndex(_)) => sub_ty.into(),
                (Type::Array(sub_ty), FieldIndex::MapEach) => sub_ty.into(),
                (Type::Map(sub_ty), FieldIndex::MapKey(_)) => sub_ty.into(),
                (Type::Map(sub_ty), FieldIndex::MapEach) => sub_ty.into(),
                (_, _) => unreachable!(),
            }
        }
        ty
    }
}

impl Serialize for IndexExpr {
    fn serialize<S: Serializer>(&self, ser: S) -> Result<S::Ok, S::Error> {
        if self.indexes.is_empty() {
            self.identifier.serialize(ser)
        } else {
            let mut seq = ser.serialize_seq(Some(self.indexes.len() + 1))?;
            match &self.identifier {
                IdentifierExpr::Field(field) => seq.serialize_element(field)?,
                IdentifierExpr::FunctionCallExpr(call) => seq.serialize_element(call)?,
            };
            for index in &self.indexes {
                seq.serialize_element(index)?;
            }
            seq.end()
        }
    }
}

enum FieldIndexIterator<'a, 'b> {
    ArrayIndex(Option<(Array<'a>, u32)>),
    MapKey(Option<(Map<'a>, &'b [u8])>),
    MapEach(IntoIter<'a>),
}

impl<'a, 'b> FieldIndexIterator<'a, 'b> {
    fn new(val: LhsValue<'a>, idx: &'b FieldIndex) -> Result<Self, IndexAccessError> {
        match idx {
            FieldIndex::ArrayIndex(idx) => match val {
                LhsValue::Array(arr) => Ok(Self::ArrayIndex(Some((arr, *idx)))),
                _ => Err(IndexAccessError {
                    index: FieldIndex::ArrayIndex(*idx),
                    actual: val.get_type(),
                }),
            },
            FieldIndex::MapKey(key) => match val {
                LhsValue::Map(map) => Ok(Self::MapKey(Some((map, key.as_bytes())))),
                _ => Err(IndexAccessError {
                    index: FieldIndex::MapKey(key.clone()),
                    actual: val.get_type(),
                }),
            },
            FieldIndex::MapEach => match val {
                LhsValue::Array(_) | LhsValue::Map(_) => Ok(Self::MapEach(val.into_iter())),
                _ => Err(IndexAccessError {
                    index: FieldIndex::MapEach,
                    actual: val.get_type(),
                }),
            },
        }
    }
}

impl<'a> Iterator for FieldIndexIterator<'a, '_> {
    type Item = LhsValue<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::ArrayIndex(opt) => opt.take().and_then(|(arr, idx)| arr.extract(idx as usize)),
            Self::MapKey(opt) => opt.take().and_then(|(map, key)| map.extract(key)),
            Self::MapEach(iter) => iter.next(),
        }
    }
}

struct MapEachIterator<'a, 'b> {
    indexes: &'b [FieldIndex],
    stack: Vec<FieldIndexIterator<'a, 'b>>,
}

impl<'a, 'b> MapEachIterator<'a, 'b> {
    fn from_indexes(indexes: &'b [FieldIndex]) -> Self {
        Self {
            indexes,
            stack: Vec::with_capacity(indexes.len()),
        }
    }

    fn reset(&mut self, val: LhsValue<'a>) {
        self.stack.clear();
        let first = self.indexes.first().unwrap();
        self.stack
            .push(FieldIndexIterator::new(val, first).unwrap());
    }
}

impl<'a> Iterator for MapEachIterator<'a, '_> {
    type Item = LhsValue<'a>;

    fn next(&mut self) -> Option<LhsValue<'a>> {
        while !self.stack.is_empty() {
            assert!(self.stack.len() <= self.indexes.len());
            if let Some(nxt) = self.stack.last_mut().unwrap().next() {
                // Check that current iterator is a leaf iterator
                if self.stack.len() == self.indexes.len() {
                    // Return a value if a leaf iterator returned a value
                    return Some(nxt);
                } else {
                    self.stack.push(
                        FieldIndexIterator::new(nxt, &self.indexes[self.stack.len()]).unwrap(),
                    );
                }
            } else {
                // Last iterator is finished, remove it
                self.stack.pop();
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        FunctionArgs, FunctionCallArgExpr, FunctionCallExpr, Scheme, SchemeBuilder,
        SimpleFunctionArgKind, SimpleFunctionDefinition, SimpleFunctionImpl, SimpleFunctionParam,
    };
    use std::sync::LazyLock;

    fn array_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        match args.next()? {
            Ok(LhsValue::Bytes(bytes)) => Some(Array::from_iter([bytes]).into()),
            Err(Type::Bytes) => None,
            _ => unreachable!(),
        }
    }

    fn array2_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        match args.next()? {
            Ok(LhsValue::Bytes(bytes)) => Some({
                let inner = Array::from_iter([bytes]);
                let outer = Array::try_from_iter(Type::Array(Type::Bytes.into()), [inner]).unwrap();
                outer.into()
            }),
            Err(Type::Bytes) => None,
            _ => unreachable!(),
        }
    }

    static SCHEME: LazyLock<Scheme> = LazyLock::new(|| {
        let mut builder = SchemeBuilder::new();
        builder
            .add_field("test", Type::Array(Type::Bytes.into()))
            .unwrap();
        builder
            .add_field("test2", Type::Array(Type::Array(Type::Bytes.into()).into()))
            .unwrap();
        builder
            .add_field("map", Type::Map(Type::Bytes.into()))
            .unwrap();
        builder
            .add_function(
                "array",
                SimpleFunctionDefinition {
                    params: vec![SimpleFunctionParam {
                        arg_kind: SimpleFunctionArgKind::Field,
                        val_type: Type::Bytes,
                    }],
                    opt_params: vec![],
                    return_type: Type::Array(Type::Bytes.into()),
                    implementation: SimpleFunctionImpl::new(array_function),
                },
            )
            .unwrap();
        builder
            .add_function(
                "array2",
                SimpleFunctionDefinition {
                    params: vec![SimpleFunctionParam {
                        arg_kind: SimpleFunctionArgKind::Field,
                        val_type: Type::Bytes,
                    }],
                    opt_params: vec![],
                    return_type: Type::Array(Type::Array(Type::Bytes.into()).into()),
                    implementation: SimpleFunctionImpl::new(array2_function),
                },
            )
            .unwrap();
        builder.build()
    });

    #[test]
    fn test_array_indices() {
        fn run(i: u32) {
            let filter = format!("test[{i}]");
            assert_ok!(
                FilterParser::new(&SCHEME).lex_as(&filter),
                IndexExpr {
                    identifier: IdentifierExpr::Field(SCHEME.get_field("test").unwrap().to_owned()),
                    indexes: vec![FieldIndex::ArrayIndex(i)],
                }
            );
        }

        run(0);
        run(1);
        run(99);
        run(999);
        run(9999);
        run(99999);

        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<IndexExpr>("test[-1]"),
            LexErrorKind::ExpectedLiteral("expected positive integer as index"),
            "-1]"
        );
    }

    #[test]
    fn test_map_access() {
        assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"map["a"]"#),
            IndexExpr {
                identifier: IdentifierExpr::Field(SCHEME.get_field("map").unwrap().to_owned()),
                indexes: vec![FieldIndex::MapKey("a".to_string())],
            }
        );

        assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"map["😍"]"#),
            IndexExpr {
                identifier: IdentifierExpr::Field(SCHEME.get_field("map").unwrap().to_owned()),
                indexes: vec![FieldIndex::MapKey("😍".to_string())],
            }
        );
    }

    #[test]
    fn test_access_with_non_string() {
        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<IndexExpr>(r#"test[a]"#),
            LexErrorKind::ExpectedLiteral("expected quoted utf8 string or positive integer"),
            "a]"
        );

        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<IndexExpr>(r#"map[a]"#),
            LexErrorKind::ExpectedLiteral("expected quoted utf8 string or positive integer"),
            "a]"
        );
    }

    #[test]
    fn test_function_call_with_missing_argument_then_index_access() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"array(test[0])[0]"#),
            IndexExpr {
                identifier: IdentifierExpr::FunctionCallExpr(FunctionCallExpr {
                    function: SCHEME.get_function("array").unwrap().to_owned(),
                    args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                        identifier: IdentifierExpr::Field(
                            SCHEME.get_field("test").unwrap().to_owned()
                        ),
                        indexes: vec![FieldIndex::ArrayIndex(0)],
                    })],
                    context: None
                }),
                indexes: vec![FieldIndex::ArrayIndex(0)],
            }
        );

        assert_eq!(expr.identifier.get_type(), Type::Array(Type::Bytes.into()));
        assert_eq!(expr.get_type(), Type::Bytes);

        let value = expr.compile();

        let mut exec_ctx = ExecutionContext::new(&SCHEME);

        exec_ctx
            .set_field_value(SCHEME.get_field("test").unwrap(), Array::new(Type::Bytes))
            .unwrap();

        assert_eq!(value.execute(&exec_ctx), Err(Type::Bytes));

        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"array(test[0])[*]"#),
            IndexExpr {
                identifier: IdentifierExpr::FunctionCallExpr(FunctionCallExpr {
                    function: SCHEME.get_function("array").unwrap().to_owned(),
                    args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                        identifier: IdentifierExpr::Field(
                            SCHEME.get_field("test").unwrap().to_owned()
                        ),
                        indexes: vec![FieldIndex::ArrayIndex(0)],
                    })],
                    context: None
                }),
                indexes: vec![FieldIndex::MapEach],
            }
        );

        assert_eq!(expr.identifier.get_type(), Type::Array(Type::Bytes.into()));
        assert_eq!(expr.get_type(), Type::Bytes);

        let value = expr.compile();

        let mut exec_ctx = ExecutionContext::new(&SCHEME);

        exec_ctx
            .set_field_value(SCHEME.get_field("test").unwrap(), Array::new(Type::Bytes))
            .unwrap();

        assert_eq!(
            value.execute(&exec_ctx),
            Err(Type::Array(Type::Bytes.into()))
        );

        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"array2(test[0])[*][*]"#),
            IndexExpr {
                identifier: IdentifierExpr::FunctionCallExpr(FunctionCallExpr {
                    function: SCHEME.get_function("array2").unwrap().to_owned(),
                    args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                        identifier: IdentifierExpr::Field(
                            SCHEME.get_field("test").unwrap().to_owned()
                        ),
                        indexes: vec![FieldIndex::ArrayIndex(0)],
                    })],
                    context: None
                }),
                indexes: vec![FieldIndex::MapEach, FieldIndex::MapEach],
            }
        );

        assert_eq!(
            expr.identifier.get_type(),
            Type::Array(Type::Array(Type::Bytes.into()).into())
        );
        assert_eq!(expr.get_type(), Type::Bytes);

        let value = expr.compile();

        let mut exec_ctx = ExecutionContext::new(&SCHEME);

        exec_ctx
            .set_field_value(SCHEME.get_field("test").unwrap(), Array::new(Type::Bytes))
            .unwrap();

        assert_eq!(
            value.execute(&exec_ctx),
            Err(Type::Array(Type::Bytes.into()))
        );

        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"array2(test[0])[*][0]"#),
            IndexExpr {
                identifier: IdentifierExpr::FunctionCallExpr(FunctionCallExpr {
                    function: SCHEME.get_function("array2").unwrap().to_owned(),
                    args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                        identifier: IdentifierExpr::Field(
                            SCHEME.get_field("test").unwrap().to_owned()
                        ),
                        indexes: vec![FieldIndex::ArrayIndex(0)],
                    })],
                    context: None
                }),
                indexes: vec![FieldIndex::MapEach, FieldIndex::ArrayIndex(0)],
            }
        );

        assert_eq!(
            expr.identifier.get_type(),
            Type::Array(Type::Array(Type::Bytes.into()).into())
        );
        assert_eq!(expr.get_type(), Type::Bytes);

        let value = expr.compile();

        let mut exec_ctx = ExecutionContext::new(&SCHEME);

        exec_ctx
            .set_field_value(SCHEME.get_field("test").unwrap(), Array::new(Type::Bytes))
            .unwrap();

        assert_eq!(
            value.execute(&exec_ctx),
            Err(Type::Array(Type::Bytes.into()))
        );

        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"array2(test[0])[0][*]"#),
            IndexExpr {
                identifier: IdentifierExpr::FunctionCallExpr(FunctionCallExpr {
                    function: SCHEME.get_function("array2").unwrap().to_owned(),
                    args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                        identifier: IdentifierExpr::Field(
                            SCHEME.get_field("test").unwrap().to_owned()
                        ),
                        indexes: vec![FieldIndex::ArrayIndex(0)],
                    })],
                    context: None
                }),
                indexes: vec![FieldIndex::ArrayIndex(0), FieldIndex::MapEach],
            }
        );

        assert_eq!(
            expr.identifier.get_type(),
            Type::Array(Type::Array(Type::Bytes.into()).into())
        );
        assert_eq!(expr.get_type(), Type::Bytes);

        let value = expr.compile();

        let mut exec_ctx = ExecutionContext::new(&SCHEME);

        exec_ctx
            .set_field_value(SCHEME.get_field("test").unwrap(), Array::new(Type::Bytes))
            .unwrap();

        assert_eq!(
            value.execute(&exec_ctx),
            Err(Type::Array(Type::Bytes.into()))
        );
    }

    #[test]
    fn test_mapeach() {
        let filter = "test2[0][*]".to_string();

        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(&filter),
            IndexExpr {
                identifier: IdentifierExpr::Field(SCHEME.get_field("test2").unwrap().to_owned()),
                indexes: vec![FieldIndex::ArrayIndex(0), FieldIndex::MapEach],
            }
        );

        assert_eq!(expr.map_each_count(), 1);
        assert_eq!(expr.get_type(), Type::Bytes);

        let filter = "test2[*][0]".to_string();

        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(&filter),
            IndexExpr {
                identifier: IdentifierExpr::Field(SCHEME.get_field("test2").unwrap().to_owned()),
                indexes: vec![FieldIndex::MapEach, FieldIndex::ArrayIndex(0)],
            }
        );

        assert_eq!(expr.map_each_count(), 1);
        assert_eq!(expr.get_type(), Type::Bytes);

        let filter = "test2[*][*]".to_string();

        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(&filter),
            IndexExpr {
                identifier: IdentifierExpr::Field(SCHEME.get_field("test2").unwrap().to_owned()),
                indexes: vec![FieldIndex::MapEach, FieldIndex::MapEach],
            }
        );

        assert_eq!(expr.map_each_count(), 2);
        assert_eq!(expr.get_type(), Type::Bytes);

        let filter = "test2[0][*][*]".to_string();

        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<IndexExpr>(&filter),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Bytes
            }),
            "[*]"
        );

        let filter = "test2[*][0][*]".to_string();

        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<IndexExpr>(&filter),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Bytes
            }),
            "[*]"
        );

        let filter = "test2[*][*][0]".to_string();

        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<IndexExpr>(&filter),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::ArrayIndex(0),
                actual: Type::Bytes
            }),
            "[0]"
        );

        let filter = "test2[*][*][*]".to_string();

        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<IndexExpr>(&filter),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Bytes
            }),
            "[*]"
        );
    }

    #[test]
    fn test_flatten() {
        let arr = LhsValue::Array(
            Array::try_from_iter(
                Type::Array(Type::Bytes.into()),
                (0..10).map(|i| Array::from_iter((0..10).map(|j| format!("[{i}][{j}]")))),
            )
            .unwrap(),
        );

        for i in 0..10 {
            let indexes = [FieldIndex::ArrayIndex(i), FieldIndex::MapEach];
            let mut iter = MapEachIterator::from_indexes(&indexes[..]);

            iter.reset(arr.clone());
            for (j, elem) in iter.enumerate() {
                let bytes = match elem {
                    LhsValue::Bytes(bytes) => bytes,
                    _ => unreachable!(),
                };
                assert_eq!(std::str::from_utf8(&bytes).unwrap(), format!("[{i}][{j}]"));
            }

            let indexes = [FieldIndex::MapEach, FieldIndex::ArrayIndex(i)];
            let mut iter = MapEachIterator::from_indexes(&indexes[..]);

            iter.reset(arr.clone());
            for (j, elem) in iter.enumerate() {
                let bytes = match elem {
                    LhsValue::Bytes(bytes) => bytes,
                    _ => unreachable!(),
                };
                assert_eq!(std::str::from_utf8(&bytes).unwrap(), format!("[{j}][{i}]"));
            }
        }

        let indexes = [FieldIndex::MapEach, FieldIndex::MapEach];
        let mut iter = MapEachIterator::from_indexes(&indexes[..]);
        let mut i = 0;
        let mut j = 0;

        iter.reset(arr.clone());
        for elem in iter {
            let bytes = match elem {
                LhsValue::Bytes(bytes) => bytes,
                _ => unreachable!(),
            };
            assert_eq!(std::str::from_utf8(&bytes).unwrap(), format!("[{i}][{j}]"));
            j = (j + 1) % 10;
            i += (j == 0) as u32;
        }
    }
}
