open Core_kernel;

module type S = {
  [@deriving (eq, bin_io, sexp, yojson, compare, hash)]
  type t;

  include Stringable.S with type t := t;

  let of_int: int => t;

  let to_int_exn: t => int;

  let (<): (t, t) => bool;

  let (+): (t, t) => t;

  let ( * ): (t, t) => t;

  let (-): (t, t) => t;

  let (/\/): (t, t) => t;

  let (%): (t, t) => t;

  let shift_left: (t, int) => t;

  let shift_right: (t, int) => t;

  let log_and: (t, t) => t;

  let log_or: (t, t) => t;

  let test_bit: (t, int) => bool;

  let num_bits: t => int;

  let of_bytes: string => t;

  let to_bytes: t => string;
};
