use std::collections::HashMap;

use cidr::{Ipv4Cidr, IpCidr, Cidr};
use serde::Serialize;

use std::net::{IpAddr, Ipv4Addr};

use crate::{types::*, ListDefinition, ListMatcher};
use crate::rhs_types::{ListName, IpRange, ExplicitIpRange};

#[derive(Debug, PartialEq, Serialize, Clone)]
pub enum ListValue {
  Ip(IpAddr),
  IpRange(IpRange)
}

/**
 * Matcher for use with lists of ints, ips and ip ranges
 */
#[derive(Debug, PartialEq, Serialize, Clone)]
pub struct IpListStore {
  lists: HashMap<String, Vec<ListValue>>
}

impl ListDefinition for IpListStore {
  fn matcher_from_json_value(
      &self,
      _ty: Type,
      _value: serde_json::Value,
  ) -> Result<crate::ListMatcherWrapper, serde_json::Error> {
      unimplemented!()
  }

  fn is_valid_matcher(&self, matcher: &dyn std::any::Any) -> bool {
    matcher.is::<IpListStore>()
  }
}

impl ListMatcher for IpListStore{
    fn match_value(&self, list_name: &str, val: &LhsValue<'_>) -> bool {
        if let Some(list) = self.lists.get(list_name) {
          match *val {
            LhsValue::Ip(target) => {
              for i in list.iter() {
                match i {
                  ListValue::Ip(i) => {
                    if *i == target {
                      return true
                    }
                  },
                  ListValue::IpRange(range) => {
                    if in_range(target, &range) {
                      return true;
                    }
                  },
                }
              }
              return false;
            },
            _ => return false
          }
        } else {
          return false;
        }
    }

    fn to_json_value(&self) -> serde_json::Value {
        serde_json::to_value(self).unwrap()
    }
}

fn in_range(ip: IpAddr, range: &IpRange) -> bool {
  match ip {
    IpAddr::V4(ip) => {
      if let IpRange::Cidr(cidr) = range {
        if let IpCidr::V4(v4) = cidr {
          return v4.contains(&ip);
        }
      } else if let IpRange::Explicit(explicit) = range {
        if let ExplicitIpRange::V4(v4_range) = explicit {
          return v4_range.contains(&ip);
        }
      }
    },
    IpAddr::V6(ip) => {
      if let IpRange::Cidr(cidr) = range {
        if let IpCidr::V6(v6) = cidr {
          return v6.contains(&ip);
        }
      } else if let IpRange::Explicit(explicit) = range {
        if let ExplicitIpRange::V6(v6_range) = explicit {
          return v6_range.contains(&ip);
        }
      }
    }
  }
  false
}

impl IpListStore{
  pub fn new() -> Self {
    return Self {
      lists: HashMap::new()
    }
  }

  pub fn add_list<'b>(&mut self, list_name: &str, list: Vec<ListValue>) {
    let name = String::from(list_name);
    self.lists.insert(name, list.clone());
  }

  pub fn add_ip_value(&mut self, list_name: &str, value: IpAddr) {
    self.add_value(list_name, ListValue::Ip(value))
  }

  pub fn add_ip_range_value(&mut self, list_name: &str, value: IpRange) {
    self.add_value(list_name, ListValue::IpRange(value))
  }

  fn add_value(&mut self, list_name: &str, value: ListValue) {
    if self.lists.get(list_name).is_none()  {
      self.add_list(list_name, vec![]);
    }
    if let Some(list) = self.lists.get_mut(list_name) {
      list.push(value)
    }
  }
}


#[cfg(test)]
use std::str::FromStr;

#[test]
fn test_ip_matching() {
  let mut matcher = IpListStore::new();
  let name: String = String::from("test_name");
  let test_cidr = Ipv4Cidr::new(Ipv4Addr::from_str("192.168.0.0").unwrap(), 24).unwrap();
  let test_range = IpRange::Cidr(IpCidr::V4(test_cidr));
  let list = vec![
    ListValue::Ip(IpAddr::from_str("10.0.0.1").unwrap()),
    ListValue::Ip(IpAddr::from_str("10.0.0.2").unwrap()),
    ListValue::IpRange(test_range),
  ];
  matcher.add_list(&name, list);

  let addr1 = IpAddr::from_str("10.0.0.2").unwrap();
  let addr2 =  IpAddr::from_str("10.0.0.10").unwrap();
  let addr3 = IpAddr::from_str("192.168.0.127").unwrap();
  let addr4 = IpAddr::from_str("192.168.1.127").unwrap();

  assert_eq!(addr1, IpAddr::from_str("10.0.0.2").unwrap());

  assert_eq!(matcher.match_value(&name, &LhsValue::Ip(addr1)), true);
  assert_eq!(matcher.match_value(&name, &LhsValue::Ip(addr2)), false);

  assert_eq!(matcher.match_value(&name, &LhsValue::Ip(addr3)), true);
  assert_eq!(matcher.match_value(&name, &LhsValue::Ip(addr4)), false);
}