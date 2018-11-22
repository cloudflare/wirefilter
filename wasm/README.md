## WebAssembly support

This is an experimental crate offering WASM bindings to the filter parser.

In order to build it, you currently need to install [wasm-pack](https://github.com/rustwasm/wasm-pack) and execute the following command in current directory:

```bash
wasm-pack build -t no-modules
```

After that, wasm-pack will generate a Node.js package in `pkg` folder that should be ready for publishing or direct usage.

If you want to just check out a simple demo, you can open [`index.html`](index.html) either directly from the filesystem or by spinning a local HTTP server.
