use std::collections::HashMap;
use serde::Serialize;

use crate::{types::*, ListDefinition, ListMatcher};

/**
 * Matcher for use with lists of ints, ips and ip ranges
 */
#[derive(Debug, PartialEq, Serialize, Clone)]
pub struct IntListStore {
  lists: HashMap<String, Vec<i32>>
}

impl ListMatcher for IntListStore{
    fn match_value(&self, list_name: &str, val: &LhsValue<'_>) -> bool {
      if let Some(list) = self.lists.get(list_name) {
        if let LhsValue::Int(target) = *val {
          let found = list.iter().find(|i| **i == target);
          if found.is_some() {
            return true
          }
        }
      }
      return false;
    }

    fn to_json_value(&self) -> serde_json::Value {
        serde_json::to_value(self).unwrap()
    }
}

impl ListDefinition for IntListStore {
    fn matcher_from_json_value(
        &self,
        _ty: Type,
        _value: serde_json::Value,
    ) -> Result<crate::ListMatcherWrapper, serde_json::Error> {
        unimplemented!()
    }

    fn is_valid_matcher(&self, matcher: &dyn std::any::Any) -> bool {
      matcher.is::<IntListStore>()
    }
}

impl IntListStore{
  pub fn new() -> Self {
    return Self {
      lists: HashMap::new()
    }
  }

  pub fn add_list<'b>(&mut self, list_name: &str, list: Vec<i32>) {
    let name = String::from(list_name);
    self.lists.insert(name, list);
  }

  pub fn add_value(&mut self, list_name: &str, value: i32) {
    if(self.lists.get(list_name).is_none()) {
      self.add_list(list_name, vec![]);
    }
    if let Some(list) = self.lists.get_mut(list_name) {
      list.push(value)
    }
  }
}

#[test]
fn test_int_matching() {
  let mut matcher = IntListStore::new();
  let test_list_1 = String::from("test_list_1");
  matcher.add_list(&test_list_1, vec![5, 10]);
  let test_list_2 = String::from("test_list_2");
  matcher.add_list(&test_list_2, vec![5, 9]);

  assert_eq!(matcher.match_value(&test_list_1, &LhsValue::Int(10)), true);
  assert_eq!(matcher.match_value(&test_list_1, &LhsValue::Int(5)), true);
  assert_eq!(matcher.match_value(&test_list_1, &LhsValue::Int(9)), false);

  assert_eq!(matcher.match_value(&test_list_2, &LhsValue::Int(10)), false);
  assert_eq!(matcher.match_value(&test_list_2, &LhsValue::Int(9)), true);
  assert_eq!(matcher.match_value(&test_list_2, &LhsValue::Int(5)), true);

  assert_eq!(matcher.match_value("missing_list", &LhsValue::Int(10)), false);
}

#[test]
fn test_other_values() {
  use std::str::FromStr;
  use std::net::IpAddr;

  let mut matcher = IntListStore::new();
  let test_list_1 = String::from("test_list_1");
  matcher.add_list(&test_list_1, vec![5, 10]);

  assert_eq!(matcher.match_value(&test_list_1, &LhsValue::Bool(true)), false);
  assert_eq!(matcher.match_value(&test_list_1, &LhsValue::Ip(IpAddr::from_str("10.0.0.2").unwrap())), false);
}