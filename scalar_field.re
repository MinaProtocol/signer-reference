open Core_kernel;
include Snarkette.Pasta.Fq;

/* Pack bits into a field element, taking the result mod the size of the field. */
let project_bits = bits => {
  module N = Nat;
  let one = N.of_int(1);
  let rec go = (acc, i) =>
    fun
    | [] => acc
    | [b, ...bs] => {
        let acc =
          if (b) {
            N.log_or(acc, N.shift_left(one, i));
          } else {
            acc;
          };
        go(acc, Int.(i + 1), bs);
      };

  let r = go(N.of_int(0), 0, bits);
  of_bigint(r);
};
