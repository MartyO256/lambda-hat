.PHONY: build test coverage format clean doc

build:
	dune build

test: build
	dune runtest --force

coverage:
	dune build --instrument-with bisect_ppx --force
	dune runtest --instrument-with bisect_ppx --force
	bisect-ppx-report html
	bisect-ppx-report summary

format:
	dune build @fmt --auto-promote

clean:
	dune clean

doc:
	dune build @doc-private
