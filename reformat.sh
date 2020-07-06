#!/bin/bash
find -name '*.ml' | grep -v _build | ocamlformat -i

