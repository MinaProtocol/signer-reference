open Core_kernel;

module type S = {
  let digest_size_in_bits: int;

  let digest_size_in_bytes: int;

  [@deriving (sexp, compare, hash)]
  type t;

  include Hashable.S with type t := t;

  include Comparable.S with type t := t;

  let bits_to_string: array(bool) => string;

  let string_to_bits: string => array(bool);

  let to_raw_string: t => string;

  let to_hex: t => string;

  let digest_string: (~off: int=?, ~len: int=?, String.t) => t;
};
