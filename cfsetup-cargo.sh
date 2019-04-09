#!/bin/bash -e

export CARGO_HOME=/var/lib/cargo
export CARGO_TARGET_DIR=$CARGO_HOME/target
export RUSTFLAGS="-D warnings"

CMD=$1
shift

set -x

case $CMD in
	prebuild)
		# Series of hacks to prebuild dependencies in a cached layer
		# (workaround for https://github.com/rust-lang/cargo/issues/2644)

		# Create dummy sources for our library
		mkdir -p {engine,ffi,ffi/tests/ctests,wasm}/src
		touch {engine,ffi,ffi/tests/ctests,wasm}/src/lib.rs
		mkdir engine/benches
		echo 'fn main() {}' > engine/benches/bench.rs

		# Build library with Cargo.lock (including all the dependencies)
		cargo build --locked --all $@

		# Clean artifacts of the library itself but keep prebuilt deps
		cargo clean --locked -p wirefilter-engine -p wirefilter-ffi -p wirefilter-wasm $@
		;;
	wasm-pack)
		# Latest release of wasm-pack can't find target via CARGO_TARGET_DIR nor
		# in a workspace root.
		#
		# This is fixed on git master, but we'd rather not build tools during
		# CI build, so let's hack around this limitation for now by creating
		# a temporary symlink and cleaning it up afterwards.
		#
		# TODO: remove following two commands on next wasm-pack upgrade.
		ln -s $CARGO_TARGET_DIR $1/target
		trap "rm $1/target" EXIT
		wasm-pack build $@
		wasm-pack pack $1
		;;
	*)
		# Execute any other command without special params but in same env
		cargo $CMD $@
		;;
esac
