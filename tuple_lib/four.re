open Core_kernel;

[@deriving (sexp, eq, bin_io, hash)]
type t =
  | Zero
  | One
  | Two
  | Three;

let of_bits_lsb: Double.t(bool) => t = (
  fun
  | (false, false) => Zero
  | (true, false) => One
  | (false, true) => Two
  | (true, true) => Three:
    Double.t(bool) => t
);
