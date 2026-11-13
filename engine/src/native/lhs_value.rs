//! Scheme-typed fields backed by existing Wirefilter values.

use super::values::{
    FieldValueType, IntoLhsValue, NativePredicate, NativeValue, ReadValue, ValueError,
};
use crate::{FieldIndex, LhsValue, Type, TypedArray};

/// A stored field whose logical type is supplied by the scheme.
///
/// Unlike a static [`super::values::ValueType`], this describes an entire field,
/// including arbitrary collection nesting, rather than a native container element.
/// Contexts must check values against the declared type when inserting them, as
/// [`crate::ExecutionContext::set_field_value`] does. Startup validation cannot
/// infer the variant returned by an arbitrary getter of [`LhsValue`].
pub struct LhsValueType;

impl FieldValueType for LhsValueType {
    type Path = Box<[FieldIndex]>;

    const DIRECT_COLLECTION_COMPARISON: bool = true;
    const STATIC_TYPE: Option<Type> = None;

    fn compile_field_path(
        mut field_type: Type,
        path: Vec<FieldIndex>,
        input_type: Type,
    ) -> Result<Self::Path, ValueError> {
        for step in &path {
            field_type = match (field_type, step) {
                (Type::Array(child), FieldIndex::ArrayIndex(_) | FieldIndex::MapEach)
                | (Type::Map(child), FieldIndex::MapKey(_) | FieldIndex::MapEach) => child.into(),
                _ => return Err(ValueError("index does not match the declared field type")),
            };
        }
        if field_type != input_type {
            return Err(ValueError(
                "predicate input type differs from selected value",
            ));
        }
        Ok(path.into_boxed_slice())
    }
}

/// Engine reader borrowing existing Wirefilter values and their containers.
pub struct LhsValueRead;

impl LhsValueRead {
    /// Compare a selected value while retaining the caller's value ownership.
    pub(crate) fn compare_one<P: NativePredicate + ?Sized>(
        value: &LhsValue<'_>,
        path: &[FieldIndex],
        predicate: &P,
    ) -> Option<bool> {
        value.get_nested(path).map(|value| predicate.lhs(value))
    }

    /// Compare selections from a possibly nested path.
    pub(crate) fn compare_vec<P: NativePredicate + ?Sized>(
        value: &LhsValue<'_>,
        path: &[FieldIndex],
        predicate: &P,
        output: &mut TypedArray<'static, bool>,
    ) {
        compare_each(value, path, predicate, output);
    }

    /// Compare each child of the collection selected by a concrete prefix.
    /// Keeping the final iteration implicit avoids retaining another path entry.
    pub(crate) fn compare_items<P: NativePredicate + ?Sized>(
        value: &LhsValue<'_>,
        prefix: &[FieldIndex],
        predicate: &P,
        output: &mut TypedArray<'static, bool>,
    ) {
        if let Some(value) = value.get_nested(prefix) {
            compare_each(value, &[FieldIndex::MapEach], predicate, output);
        }
    }
}

impl NativeValue for LhsValue<'_> {
    type Read = LhsValueRead;
    type ValueType = LhsValueType;
}

impl<'a, 'data: 'a> IntoLhsValue<'a> for LhsValue<'data> {
    const MATERIALIZES_COLLECTIONS: bool = false;

    #[inline]
    fn into_lhs(self) -> LhsValue<'a> {
        self
    }

    #[inline]
    fn append_lhs_at(self, indexes: &[FieldIndex], output: &mut Vec<LhsValue<'a>>) {
        super::values::append_stored_lhs_at(self, indexes, output);
    }
}

impl ReadValue<LhsValue<'_>, LhsValueType> for LhsValueRead {
    const MATERIALIZES_COLLECTIONS: bool = false;

    #[inline]
    fn to_lhs<'a>(value: &'a LhsValue<'_>) -> LhsValue<'a> {
        value.as_ref()
    }

    #[inline]
    fn to_lhs_at<'a>(value: &'a LhsValue<'_>, indexes: &[FieldIndex]) -> Option<LhsValue<'a>> {
        value.get_nested(indexes).map(LhsValue::as_ref)
    }

    #[inline]
    fn append_lhs_at<'a>(
        value: &'a LhsValue<'_>,
        indexes: &[FieldIndex],
        output: &mut Vec<LhsValue<'a>>,
    ) {
        super::values::append_stored_lhs_at(value.as_ref(), indexes, output);
    }

    #[inline]
    fn compare_one<P: NativePredicate + ?Sized>(
        value: &LhsValue<'_>,
        path: &Box<[FieldIndex]>,
        predicate: &P,
    ) -> Option<bool> {
        Self::compare_one(value, path, predicate)
    }

    #[inline]
    fn compare_vec<P: NativePredicate + ?Sized>(
        value: &LhsValue<'_>,
        path: &Box<[FieldIndex]>,
        predicate: &P,
        output: &mut TypedArray<'static, bool>,
    ) {
        Self::compare_vec(value, path, predicate, output);
    }
}

fn compare_each<'a, P: NativePredicate + ?Sized>(
    mut value: &'a LhsValue<'a>,
    mut path: &[FieldIndex],
    predicate: &P,
    output: &mut TypedArray<'static, bool>,
) {
    // Follow concrete indices while reading values, without first searching for
    // [*]. Only collection iteration recurses; concrete indices add no calls.
    while let Some((index, rest)) = path.split_first() {
        if *index == FieldIndex::MapEach {
            let children = value.iter().expect("[*] requires a collection");
            if rest.is_empty() {
                if output.is_empty() {
                    *output = TypedArray::with_capacity(children.size_hint().0);
                }
                for child in children {
                    output.push(predicate.lhs(child));
                }
            } else {
                for child in children {
                    compare_each(child, rest, predicate, output);
                }
            }
            return;
        }
        let Some(child) = value.get(index).unwrap() else {
            return;
        };
        value = child;
        path = rest;
    }
    output.push(predicate.lhs(value));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn validates_paths_against_the_scheme_type() {
        let root = Type::map(Type::array(Type::Int));
        let path = vec![FieldIndex::MapKey("values".into()), FieldIndex::MapEach];
        assert_eq!(
            LhsValueType::compile_field_path(root, path.clone(), Type::Int).unwrap(),
            path.into_boxed_slice(),
        );
        assert!(LhsValueType::compile_field_path(root, vec![], root).is_ok());
        assert!(LhsValueType::compile_field_path(root, vec![], Type::Int).is_err());
        assert!(
            LhsValueType::compile_field_path(
                root,
                vec![FieldIndex::ArrayIndex(0)],
                Type::array(Type::Int),
            )
            .is_err()
        );
        assert!(
            LhsValueType::compile_field_path(Type::Int, vec![FieldIndex::MapEach], Type::Int,)
                .is_err()
        );
        assert!(
            LhsValueType::compile_field_path(
                Type::array(Type::Int),
                vec![FieldIndex::MapKey("values".into())],
                Type::Int,
            )
            .is_err()
        );
    }
}
