module Compressed = struct
  (* the x coordinate and y-parity of a curve point *)
  type t = {x: Base_field.t; is_odd: bool} [@@deriving yojson]
end
