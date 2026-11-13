//! Custom collection comparisons select native storage before materialization.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::sync::Arc;
use wirefilter::native::values::{
    self, ArrayRead, IntoLhsValue, MapRead, NativeArray, NativeMap, NativeValue, ValueType,
};
use wirefilter::{
    Compare, CompiledExpr, ContextFamily, DefaultCompiler, EvaluationContext, ExecutionContext,
    FieldIndex, HasScheme, IdentifierExpr, IndexExpr, LhsValue, List, ListMatcher, ListRef,
    NativeContextState, Scheme, SchemeBuilder, Type,
};

thread_local! {
    static MATERIALIZED: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };
}

struct CountedArray<T> {
    label: String,
    items: Vec<T>,
}

impl<T: NativeValue> NativeValue for CountedArray<T>
where
    T::ValueType: ValueType,
{
    type Read = ArrayRead;
    type ValueType = values::Array<T::ValueType>;
}

impl<T: NativeValue> NativeArray for CountedArray<T>
where
    T::ValueType: ValueType,
{
    type Element = T::ValueType;
    type Item<'a>
        = &'a T
    where
        Self: 'a;
    type Iter<'a>
        = std::slice::Iter<'a, T>
    where
        Self: 'a;

    fn get(&self, index: usize) -> Option<Self::Item<'_>> {
        self.items.get(index)
    }

    fn iter(&self) -> Self::Iter<'_> {
        MATERIALIZED.with_borrow_mut(|values| values.push(self.label.clone()));
        self.items.iter()
    }
}

type Row = CountedArray<String>;
type Section = CountedArray<Row>;
type Group = CountedArray<Section>;
type Groups = BTreeMap<Box<[u8]>, Group>;

// This by-value descriptor intentionally keeps the default into_lhs_at method.
#[derive(Clone)]
struct Descriptor(Arc<Groups>);

impl NativeValue for Descriptor {
    type Read = MapRead;
    type ValueType = values::Map<<Group as NativeValue>::ValueType>;
}

impl IntoLhsValue<'_> for Descriptor {}

impl NativeMap for Descriptor {
    type Element = <Group as NativeValue>::ValueType;
    type Item<'a> = &'a Group;
    type Iter<'a> = std::collections::btree_map::Values<'a, Box<[u8]>, Group>;

    fn get(&self, key: &[u8]) -> Option<Self::Item<'_>> {
        self.0.get(key)
    }

    fn values(&self) -> Self::Iter<'_> {
        self.0.values()
    }

    fn for_each_entry<'a>(&'a self, mut visitor: impl FnMut(&[u8], Self::Item<'a>)) {
        for (key, value) in self.0.iter() {
            visitor(key, value);
        }
    }
}

struct Context {
    state: NativeContextState<()>,
    groups: Option<Arc<Groups>>,
}

impl HasScheme for Context {
    fn scheme(&self) -> &Scheme {
        self.state.scheme()
    }
}

impl EvaluationContext for Context {
    type UserData = ();

    fn get_user_data(&self) -> &() {
        &()
    }

    fn get_list_matcher(&self, list: ListRef<'_>) -> &dyn ListMatcher {
        self.state.get_list_matcher(list)
    }

    fn get_list_matcher_unchecked(&self, list: &List) -> &dyn ListMatcher {
        EvaluationContext::get_list_matcher_unchecked(&self.state, list)
    }
}

wirefilter::wirefilter_fields! {
    impl Fields for Context {
        "groups" => {
            fn(context: &Context) -> Option<&Groups> {
                context.groups.as_deref()
            }
        },
        "owned" => {
            fn(context: &Context) -> Option<Descriptor> {
                context.groups.clone().map(Descriptor)
            }
        },
    }
}

struct Nonempty;

impl<F: ContextFamily<UserData = ()>> Compare<(), F> for Nonempty {
    fn compare<'ctx, 'data: 'ctx>(
        &self,
        value: &LhsValue<'ctx>,
        _: &'ctx F::Context<'data>,
    ) -> bool {
        match value {
            LhsValue::Array(array) => !array.is_empty(),
            LhsValue::Map(map) => !map.is_empty(),
            _ => panic!("custom comparator requires a collection"),
        }
    }
}

fn fixture(present: bool) -> Context {
    let mut builder = SchemeBuilder::new();
    let ty = Type::map(Type::array(Type::array(Type::array(Type::Bytes))));
    builder.add_optional_field("groups", ty).unwrap();
    builder.add_optional_field("owned", ty).unwrap();
    let scheme = builder.build();
    Fields::validate_scheme(&scheme).unwrap();
    let groups = present.then(|| {
        Arc::new(
            ["wanted", "other"]
                .into_iter()
                .map(|name| {
                    let group = CountedArray {
                        label: name.into(),
                        items: (0..2)
                            .map(|section| CountedArray {
                                label: format!("{name}/{section}"),
                                items: (0..2)
                                    .map(|row| CountedArray {
                                        label: format!("{name}/{section}/{row}"),
                                        items: if row == 0 {
                                            vec!["value".into()]
                                        } else {
                                            vec![]
                                        },
                                    })
                                    .collect(),
                            })
                            .collect(),
                    };
                    (Box::<[u8]>::from(name.as_bytes()), group)
                })
                .collect(),
        )
    });
    Context {
        state: NativeContextState::new(&scheme),
        groups,
    }
}

fn evaluate(native: &Context, field: &str, indexes: Vec<FieldIndex>, default: bool) -> Vec<String> {
    let scheme = native.scheme();
    let mut stored = ExecutionContext::new(scheme);
    if let Some(groups) = &native.groups {
        stored
            .set_field_value_from_name(field, groups.as_ref().into_lhs())
            .unwrap();
    }
    let index = IndexExpr {
        identifier: IdentifierExpr::Field(scheme.get_field(field).unwrap().to_owned()),
        indexes: indexes.into_boxed_slice(),
    };
    let stored_expr =
        index
            .clone()
            .compile_with(&mut DefaultCompiler::<()>::new(), default, Nonempty);
    let native_expr =
        index.compile_with(&mut DefaultCompiler::<(), Fields>::new(), default, Nonempty);
    MATERIALIZED.with_borrow_mut(Vec::clear);
    match (stored_expr, native_expr) {
        (CompiledExpr::One(stored_expr), CompiledExpr::One(native_expr)) => {
            assert_eq!(stored_expr.execute(&stored), native_expr.execute(native));
        }
        (CompiledExpr::Vec(stored_expr), CompiledExpr::Vec(native_expr)) => {
            assert_eq!(stored_expr.execute(&stored), native_expr.execute(native));
        }
        _ => panic!("comparison cardinality changed"),
    }
    MATERIALIZED.with_borrow_mut(std::mem::take)
}

#[test]
fn borrowed_comparisons_only_materialize_the_selected_subtree() {
    use FieldIndex::{ArrayIndex as At, MapEach as Each, MapKey};
    let native = fixture(true);
    for (path, selected) in [
        (vec![MapKey("wanted".into()), At(0), At(0)], "wanted/0/0"),
        (vec![MapKey("wanted".into()), At(0), Each], "wanted/0"),
        (vec![MapKey("wanted".into()), Each, At(0)], "wanted"),
        (vec![MapKey("wanted".into()), Each, Each], "wanted"),
        // Missing children after [*] still produce the same empty comparison vector.
        (vec![MapKey("wanted".into()), Each, At(99)], "wanted"),
    ] {
        let materialized = evaluate(&native, "groups", path, false);
        assert!(!materialized.is_empty());
        assert!(
            materialized.iter().all(|name| name.starts_with(selected)),
            "converted unrelated containers: {materialized:?}"
        );
    }
}

#[test]
fn missing_selections_and_optional_roots_keep_stored_comparison_semantics() {
    use FieldIndex::{ArrayIndex as At, MapEach as Each, MapKey};
    let present = fixture(true);
    let absent = fixture(false);
    for default in [false, true] {
        for path in [
            vec![MapKey("missing".into()), At(0)],
            vec![MapKey("wanted".into()), At(99)],
            vec![MapKey("missing".into()), Each],
            vec![MapKey("missing".into()), Each, At(0)],
            vec![MapKey("wanted".into()), At(99), Each],
        ] {
            assert!(evaluate(&present, "groups", path, default).is_empty());
        }
        for path in [
            vec![MapKey("wanted".into()), At(0)],
            vec![MapKey("wanted".into()), Each],
            vec![MapKey("wanted".into()), Each, At(0)],
        ] {
            assert!(evaluate(&absent, "groups", path, default).is_empty());
        }
    }
}

#[test]
fn by_value_descriptors_keep_the_default_conversion_before_selection() {
    use FieldIndex::{ArrayIndex as At, MapEach as Each, MapKey};
    let native = fixture(true);
    for path in [
        vec![MapKey("wanted".into()), At(0), At(0)],
        vec![MapKey("wanted".into()), At(0), Each],
        vec![MapKey("wanted".into()), Each, At(0)],
    ] {
        let materialized = evaluate(&native, "owned", path, false);
        assert!(materialized.iter().any(|name| name == "wanted"));
        assert!(materialized.iter().any(|name| name == "other"));
    }
}

#[test]
fn comparisons_without_a_concrete_prefix_still_materialize_the_whole_map() {
    let native = fixture(true);
    for path in [vec![], vec![FieldIndex::MapEach]] {
        let materialized = evaluate(&native, "groups", path, false);
        assert!(materialized.iter().any(|name| name == "wanted"));
        assert!(materialized.iter().any(|name| name == "other"));
    }
}
