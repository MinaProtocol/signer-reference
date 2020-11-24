open Core_kernel;

module Make = (()) => {
  let digest_size_in_bits = 256;

  let digest_size_in_bytes = digest_size_in_bits / 8;

  module T0 = {
    include Digestif.Make_BLAKE2B({
      let digest_size = digest_size_in_bytes;
    });

    let hash = Fn.compose(String.hash, to_raw_string);

    let hash_fold_t = (state, t) =>
      Hash.fold_string(state, to_raw_string(t));

    let compare = unsafe_compare;

    let of_string = of_raw_string;

    let to_string = to_raw_string;
  };

  module T1 = {
    include T0;
    include Sexpable.Of_stringable(T0);
  };

  [@deriving (hash, sexp, compare)]
  type t = T1.t;

  let to_raw_string = T1.to_raw_string;

  let digest_string = T1.digest_string;

  let to_hex = T1.to_hex;

  /* do not create bin_io serialization */
  include Hashable.Make(T1);
  include Comparable.Make(T1);

  /* Little endian */
  let bits_to_string = bits => {
    let n = Array.length(bits);
    let rec make_byte = (offset, acc, i: int) => {
      let finished = Int.(i == 8 || offset + i >= n);
      if (finished) {
        Char.of_int_exn(acc);
      } else {
        let acc =
          if (bits[offset + i]) {
            acc lor 1 lsl i;
          } else {
            acc;
          };
        make_byte(offset, acc, i + 1);
      };
    };

    let len = (n + 7) / 8;
    String.init(len, ~f=i => make_byte(8 * i, 0, 0));
  };

  let string_to_bits = s =>
    Array.init(
      8 * String.length(s),
      ~f=i => {
        let c = Char.to_int(s.[i / 8]);
        let j = i mod 8;
        Int.(c lsr j land 1 == 1);
      },
    );
};

include Make({});
