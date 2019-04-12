use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub struct Scheme(wirefilter::Scheme);

#[allow(clippy::needless_pass_by_value)]
fn into_js_error(err: impl std::error::Error) -> JsValue {
    js_sys::Error::new(&err.to_string()).into()
}

#[wasm_bindgen]
impl Scheme {
    #[wasm_bindgen(constructor)]
    pub fn try_from(fields: &JsValue) -> Result<Scheme, JsValue> {
        fields.into_serde().map(Scheme).map_err(into_js_error)
    }

    pub fn parse(&self, s: &str) -> Result<JsValue, JsValue> {
        let filter = self.0.parse(s).map_err(into_js_error)?;
        JsValue::from_serde(&filter).map_err(into_js_error)
    }
}
