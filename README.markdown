# Reference signer

This is a standalone reference signer implementation for Coda's schnorr signatures. It includes implementations of the
[tweedle curves and fields](https://github.com/daira/tweedle), the Poseidon hash function, and Schnorr signatures.

Here are instructions on how to use it

## Installing dependencies
First install opam. You can use the guide [here](https://opam.ocaml.org/doc/Install.html) or just run
```bash
sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
```
and run `opam init`.

Next, install the dependency libraries:
```bash
opam install core digestif ppx_jane ppx_deriving_yojson
```

## Building
Build with
```
dune build ./schnorr.exe
```
This will build the binary in `_build/default/schnorr.exe`

## Running

Run with
```
_build/default/schnorr.exe PATH_TO_TRANSACTION_JSON -privkey PRIVKEY_AS_A_DECIMAL_STRING
```

If the `-privkey` option is omitted, a random private key will be used. The program simply
signs the transaction and immediately verifies it.

See `example.json` for a sample JSON file.
