open Core_kernel

module UInt64 = struct
  type t = Int64.t [@@deriving yojson]

  let of_int = Int64.of_int

  let of_string = Int64.of_string

  let to_bits x = List.init 64 ~f:(fun i -> Int64.((x lsr i) land one = one))
end

module UInt32 = struct
  type t = Int32.t [@@deriving yojson]

  let of_int x = Option.value_exn (Int32.of_int x)

  let of_string = Int32.of_string

  let to_bits x = List.init 32 ~f:(fun i -> Int32.((x lsr i) land one = one))
end

module Amount = UInt64
module Fee = UInt64
module Global_slot = UInt32
module Token_id = UInt64
module Nonce = UInt32

module Memo : sig
  type t [@@deriving yojson]

  val of_string : string -> t

  val to_bits : t -> bool list
end = struct
  let length = 34

  type t = string [@@deriving yojson]

  let of_string s =
    assert (String.length s = length) ;
    s

  let fold_bits t =
    { Fold_lib.Fold.fold=
        (fun ~init ~f ->
          let n = 8 * String.length t in
          let rec go acc i =
            if i = n then acc
            else
              let b = (Char.to_int t.[i / 8] lsr (i mod 8)) land 1 = 1 in
              go (f acc b) (i + 1)
          in
          go init 0 ) }

  let to_bits t = Fold_lib.Fold.to_list (fold_bits t)
end

module Tag = struct
  type t = bool * bool * bool [@@deriving yojson]

  let to_bits (b1, b2, b3) = [b1; b2; b3]
end

module Payload = struct
  module Common = struct
    type t =
      { fee: Fee.t
      ; fee_token: Token_id.t
      ; fee_payer_pk: Public_key.Compressed.t
      ; nonce: Nonce.t
      ; valid_until: Global_slot.t
      ; memo: Memo.t }
    [@@deriving yojson]
  end

  module Body = struct
    type t =
      { tag: Tag.t
      ; source_pk: Public_key.Compressed.t
      ; receiver_pk: Public_key.Compressed.t
      ; token_id: Token_id.t
      ; amount: Amount.t }
    [@@deriving yojson]
  end

  type t = {common: Common.t; body: Body.t} [@@deriving yojson]

  let to_input
      { common= {fee; fee_token; fee_payer_pk; nonce; valid_until; memo}
      ; body= {tag; source_pk; receiver_pk; token_id; amount} } =
    { Random_oracle_input.field_elements=
        [|fee_payer_pk.x; source_pk.x; receiver_pk.x|]
    ; bitstrings=
        [| Fee.to_bits fee
         ; Token_id.to_bits fee_token
         ; [fee_payer_pk.is_odd]
         ; Nonce.to_bits nonce
         ; Global_slot.to_bits valid_until
         ; Memo.to_bits memo
         ; Tag.to_bits tag
         ; [source_pk.is_odd]
         ; [receiver_pk.is_odd]
         ; Token_id.to_bits token_id
         ; Amount.to_bits amount |] }
end
