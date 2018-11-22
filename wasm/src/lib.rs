extern crate wasm_bindgen;
extern crate wirefilter;

use wasm_bindgen::prelude::*;
use wirefilter::Scheme;

#[wasm_bindgen]
pub fn parse_filter(fields: &JsValue, s: &str) -> JsValue {
    let scheme: Scheme = fields.into_serde().unwrap();
    let filter = scheme.parse(s).unwrap();
    JsValue::from_serde(&filter).unwrap()
}
