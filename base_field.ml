open Core_kernel
include Snarkette.Tweedle.Fq

(* Pack bits into a field element, taking the result mod the size of the field. *)
let project_bits bits =
  let module N = Snarkette.Tweedle.Fq.Nat in
  let one = N.of_int 1 in
  let rec go acc i = function
    | [] ->
        acc
    | b :: bs ->
        let acc = if b then N.log_or acc (N.shift_left one i) else acc in
        go acc Int.(i + 1) bs
  in
  let r = go (N.of_int 0) 0 bits in
  of_bigint r

let to_yojson t : Yojson.Safe.t = `String (to_string t)

let of_yojson j =
  match j with `String h -> Ok (of_string h) | _ -> Error "expected string"
