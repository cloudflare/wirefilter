extern crate js_sys;
extern crate wasm_bindgen;
extern crate wirefilter;

use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub struct Scheme(wirefilter::Scheme);

#[cfg_attr(feature = "cargo-clippy", allow(needless_pass_by_value))]
fn into_js_error(err: impl std::error::Error) -> JsValue {
    js_sys::Error::new(&err.to_string()).into()
}

#[wasm_bindgen]
impl Scheme {
    #[wasm_bindgen(constructor)]
    pub fn new(fields: &JsValue) -> Result<Scheme, JsValue> {
        fields.into_serde().map(Scheme).map_err(into_js_error)
    }

    pub fn parse(&self, s: &str) -> Result<JsValue, JsValue> {
        let filter = self.0.parse(s).map_err(into_js_error)?;
        JsValue::from_serde(&filter).map_err(into_js_error)
    }
}
