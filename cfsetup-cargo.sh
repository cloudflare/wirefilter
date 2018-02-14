#!/bin/bash
set -e

export CARGO_HOME=/var/lib/cargo
export CARGO_TARGET_DIR=$CARGO_HOME/target

CMD=$1
shift

if [ $CMD = prebuild ]
then
	# Series of hacks to prebuild dependencies in a cached layer
	# (workaround for https://github.com/rust-lang/cargo/issues/2644)

	# Create dummy sources for our library
	mkdir {engine,ffi}/src
	touch {engine,ffi}/src/lib.rs

	# Build library with Cargo.lock (including all the dependencies)
	cargo build -q --locked --all "$@"

	# Clean artifacts of the library itself but keep prebuilt deps
	cargo clean -p wirefilter-engine -p wirefilter-ffi "$@"
else
	# Execute any other command assuming that any deps are already in cache
	cargo $CMD --frozen "$@"
fi
