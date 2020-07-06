#!/bin/bash
find -name '*.ml' | grep -v _build | xargs ocamlformat -i

