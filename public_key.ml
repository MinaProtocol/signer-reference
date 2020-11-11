open Core_kernel

(* A point on the curve *)
type t = Snarkette.Tweedle.Dee.t

module Compressed = struct
  (* the x coordinate and y-parity of a curve point *)
  module T = struct
    type t = {x: Base_field.t; is_odd: bool} [@@deriving bin_io]
  end

  let version_byte = '\xCB'

  let to_base58_check = Base58_check.to_base58_check ~version_byte (module T)

  let of_base58_check = Base58_check.of_base58_check ~version_byte (module T)

  include T

  let to_yojson x = `String (to_base58_check x)

  let of_yojson : Yojson.Safe.t -> _ = function
    | `String s ->
        Ok (of_base58_check s)
    | _ ->
        Error "bad public key"
end
