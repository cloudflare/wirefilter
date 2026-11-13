//! Native map traversal and materialization preserve provider order and key ownership.

use indexmap::IndexMap;
use std::cell::RefCell;
use wirefilter::values::{self, IntoLhsValue, MapRead, MapValue, Value};
use wirefilter::{
    Bytes, ContextState, DefaultCompiler, EvaluationContext, FunctionArgs, HasScheme, LhsValue,
    List, ListMatcher, ListRef, Scheme, SchemeBuilder, SimpleFunctionArgKind,
    SimpleFunctionDefinition, SimpleFunctionImpl, SimpleFunctionParam, Type,
};

const ENTRIES: [(&[u8], &[u8]); 3] = [(b"z", b"target"), (b"a", b"other"), (b"m", b"last")];

struct OrderedMap {
    keys: Vec<Box<[u8]>>,
    values: Vec<Box<[u8]>>,
}

impl OrderedMap {
    fn new() -> Self {
        let (keys, values) = ENTRIES
            .iter()
            .map(|&(key, value)| (Box::from(key), Box::from(value)))
            .unzip();
        Self { keys, values }
    }
}

impl Value for OrderedMap {
    type Read = MapRead;
    type ValueType = values::Map<values::Bytes>;
}

impl MapValue for OrderedMap {
    type Element = values::Bytes;
    type Item<'a> = &'a Box<[u8]>;
    type Iter<'a> = std::slice::Iter<'a, Box<[u8]>>;

    fn get(&self, key: &[u8]) -> Option<Self::Item<'_>> {
        self.keys
            .iter()
            .position(|candidate| candidate.as_ref() == key)
            .map(|index| &self.values[index])
    }

    fn values(&self) -> Self::Iter<'_> {
        self.values.iter()
    }

    fn for_each_entry<'a>(&'a self, mut visitor: impl FnMut(Bytes<'a>, Self::Item<'a>)) {
        for (key, value) in self.keys.iter().zip(&self.values) {
            visitor(Bytes::Borrowed(key), value);
        }
    }
}

struct Context {
    state: ContextState<()>,
    ordered: OrderedMap,
    indexed: IndexMap<Box<[u8]>, Box<[u8]>>,
}

impl HasScheme for Context {
    fn scheme(&self) -> &Scheme {
        self.state.scheme()
    }
}

impl EvaluationContext for Context {
    type UserData = ();

    fn get_user_data(&self) -> &() {
        self.state.get_user_data()
    }

    fn get_list_matcher(&self, list: ListRef<'_>) -> &dyn ListMatcher {
        self.state.get_list_matcher(list)
    }

    fn get_list_matcher_unchecked(&self, list: &List) -> &dyn ListMatcher {
        self.state.get_list_matcher_unchecked(list)
    }
}

wirefilter::wirefilter_fields! {
    impl Fields for Context {
        "ordered" => {
            fn(ctx: &Context) -> &OrderedMap {
                &ctx.ordered
            }
        },
        "indexed" => {
            fn(ctx: &Context) -> &IndexMap<Box<[u8]>, Box<[u8]>> {
                &ctx.indexed
            }
        },
    }
}

fn identity<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
    args.next()?.ok()
}

fn context() -> Context {
    let map_type = Type::map(Type::Bytes);
    let mut builder = SchemeBuilder::new();
    for name in ["ordered", "indexed"] {
        builder.add_field(name, map_type).unwrap();
    }
    builder
        .add_function(
            "echo_map",
            SimpleFunctionDefinition {
                params: Box::new([SimpleFunctionParam {
                    arg_kind: SimpleFunctionArgKind::Field,
                    val_type: map_type,
                }]),
                opt_params: Box::new([]),
                return_type: map_type,
                implementation: SimpleFunctionImpl::new(identity),
            },
        )
        .unwrap();
    let scheme = builder.build();
    Fields::validate_scheme(&scheme).unwrap();
    Context {
        state: ContextState::new(&scheme),
        ordered: OrderedMap::new(),
        indexed: ENTRIES
            .iter()
            .map(|&(key, value)| (Box::from(key), Box::from(value)))
            .collect(),
    }
}

#[test]
fn test_native_map_order_matches_materialized_function_results() {
    let context = context();
    for name in ["ordered", "indexed"] {
        // Each predicate selects a different position. Sorting the materialized
        // map would make the XOR true for at least one of these expressions.
        for expected in ["target", "other", "last"] {
            let expression = format!(
                r#"any(({name}[*] eq "{expected}") xor (echo_map({name})[*] eq "{expected}"))"#,
            );
            let filter = context
                .scheme()
                .parse(&expression)
                .unwrap()
                .compile_with_compiler(&mut DefaultCompiler::<(), Fields>::new());
            assert!(!filter.execute(&context).unwrap(), "{expression}");
        }
        for (key, expected) in [("a", true), ("A", false)] {
            let expression = format!(r#"{name}["{key}"] eq "other""#);
            let filter = context
                .scheme()
                .parse(&expression)
                .unwrap()
                .compile_with_compiler(&mut DefaultCompiler::<(), Fields>::new());
            assert_eq!(filter.execute(&context).unwrap(), expected, "{expression}");
        }

        let expression = format!("echo_map({name})");
        let value = context
            .scheme()
            .parse_value(&expression)
            .unwrap()
            .compile_with_compiler(&mut DefaultCompiler::<(), Fields>::new());
        let LhsValue::Map(map) = value.execute(&context).unwrap().unwrap() else {
            panic!("identity must retain the map");
        };
        let source: Vec<_> = if name == "ordered" {
            context
                .ordered
                .keys
                .iter()
                .zip(&context.ordered.values)
                .collect()
        } else {
            context.indexed.iter().collect()
        };
        assert_eq!(map.len(), source.len());
        for (((key, value), (source_key, source_value)), &(expected_key, expected_value)) in
            map.into_iter().zip(source).zip(&ENTRIES)
        {
            let Bytes::Borrowed(key) = key else {
                panic!("materialization must borrow a native key");
            };
            let LhsValue::Bytes(Bytes::Borrowed(value)) = value else {
                panic!("materialization must borrow a native byte value");
            };
            assert_eq!(key, expected_key);
            assert_eq!(value, expected_value);
            assert!(std::ptr::eq(key, source_key.as_ref()));
            assert!(std::ptr::eq(value, source_value.as_ref()));
        }
    }
}

#[test]
fn test_materialized_borrowed_keys_can_be_owned_after_source_is_dropped() {
    let owned = {
        let source = OrderedMap::new();
        (&source).into_lhs().into_owned()
    };
    let LhsValue::Map(map) = owned else {
        panic!("expected an owned map");
    };
    assert_eq!(map.len(), ENTRIES.len());
    for ((key, value), &(expected_key, expected_value)) in map.into_iter().zip(&ENTRIES) {
        assert!(matches!(key, Bytes::Owned(_)));
        assert_eq!(key.as_ref(), expected_key);
        let LhsValue::Bytes(Bytes::Owned(value)) = value else {
            panic!("owned map must own the byte value");
        };
        assert_eq!(value.as_ref(), expected_value);
    }
}

// The provider generates each key during visitation. Bytes::Owned permits
// transferring that allocation even though the provider itself is borrowed.
struct GeneratedKeys {
    values: [Box<[u8]>; 3],
    key_addresses: RefCell<Vec<usize>>,
}

impl Value for GeneratedKeys {
    type Read = MapRead;
    type ValueType = values::Map<values::Bytes>;
}

impl MapValue for GeneratedKeys {
    type Element = values::Bytes;
    type Item<'a> = &'a Box<[u8]>;
    type Iter<'a> = std::slice::Iter<'a, Box<[u8]>>;

    fn get(&self, key: &[u8]) -> Option<Self::Item<'_>> {
        ENTRIES
            .iter()
            .position(|&(candidate, _)| candidate == key)
            .map(|index| &self.values[index])
    }

    fn values(&self) -> Self::Iter<'_> {
        self.values.iter()
    }

    fn for_each_entry<'a>(&'a self, mut visitor: impl FnMut(Bytes<'a>, Self::Item<'a>)) {
        self.key_addresses.borrow_mut().clear();
        for (&(key, _), value) in ENTRIES.iter().zip(&self.values) {
            let key = Box::<[u8]>::from(key);
            self.key_addresses.borrow_mut().push(key.as_ptr() as usize);
            visitor(Bytes::Owned(key), value);
        }
    }
}

#[test]
fn test_materialization_moves_generated_owned_keys() {
    let (owned, key_addresses) = {
        let source = GeneratedKeys {
            values: ENTRIES.map(|(_, value)| Box::from(value)),
            key_addresses: RefCell::new(Vec::new()),
        };
        let converted = (&source).into_lhs();
        let key_addresses = source.key_addresses.borrow().clone();
        let LhsValue::Map(map) = &converted else {
            panic!("expected a materialized map");
        };
        for ((key, _), &address) in map.iter().zip(&key_addresses) {
            assert_eq!(key.as_ptr() as usize, address, "generated key was copied");
        }
        (converted.into_owned(), key_addresses)
    };
    let LhsValue::Map(map) = owned else {
        panic!("expected an owned map");
    };
    assert_eq!(map.len(), ENTRIES.len());
    for (((key, value), address), &(expected_key, expected_value)) in
        map.into_iter().zip(key_addresses).zip(&ENTRIES)
    {
        let Bytes::Owned(key) = key else {
            panic!("generated key must remain owned");
        };
        assert_eq!(
            key.as_ptr() as usize,
            address,
            "into_owned copied an owned key"
        );
        assert_eq!(key.as_ref(), expected_key);
        let LhsValue::Bytes(Bytes::Owned(value)) = value else {
            panic!("owned map must own the byte value");
        };
        assert_eq!(value.as_ref(), expected_value);
    }
}
