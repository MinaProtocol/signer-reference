open Core_kernel

module UInt64 = struct
  type t = Int64.t

  let of_int = Int64.of_int

  let of_string = Int64.of_string

  let to_yojson x = `String (Int64.to_string x)

  let of_yojson : Yojson.Safe.t -> _ = function
    | `String s ->
        Ok (of_string s)
    | _ ->
        Error "bad uint64 string"

  let to_bits x = List.init 64 ~f:(fun i -> Int64.((x lsr i) land one = one))
end

module Currency = struct
  type t = Int64.t [@@deriving sexp, compare]

  let to_bits = UInt64.to_bits

  let of_int = Int64.of_int

  let precision = 9

  let precision_exp = Int64.of_int @@ Int.pow 10 precision

  let to_formatted_string amount =
    let rec go num_stripped_zeros num =
      let open Int in
      if num mod 10 = 0 && num <> 0 then go (num_stripped_zeros + 1) (num / 10)
      else (num_stripped_zeros, num)
    in
    let whole = Int64.( / ) amount precision_exp in
    let remainder =
      Int64.to_int (Int64.rem amount precision_exp) |> Option.value_exn
    in
    if Int.(remainder = 0) then Int64.to_string whole
    else
      let num_stripped_zeros, num = go 0 remainder in
      Printf.sprintf "%s.%0*d" (Int64.to_string whole)
        Int.(precision - num_stripped_zeros)
        num

  let of_formatted_string input =
    let of_string = Int64.of_string in
    let parts = String.split ~on:'.' input in
    match parts with
    | [whole] ->
        of_string (whole ^ String.make precision '0')
    | [whole; decimal] ->
        let decimal_length = String.length decimal in
        if Int.(decimal_length > precision) then
          of_string (whole ^ String.sub decimal ~pos:0 ~len:precision)
        else
          of_string
            (whole ^ decimal ^ String.make Int.(precision - decimal_length) '0')
    | _ ->
        failwith "Currency.of_formatted_string: Invalid currency input"

  let to_yojson x = `String (to_formatted_string x)

  let of_yojson : Yojson.Safe.t -> _ = function
    | `String s ->
        Ok (of_formatted_string s)
    | _ ->
        Error "bad currency string"

  let () =
    let t = of_int 42 in
    [%test_eq: t] t
      (Or_error.ok_exn
         (Result.map_error ~f:Error.of_string (of_yojson (to_yojson t))))
end

module UInt32 = struct
  type t = Int32.t

  let to_yojson (x : t) = `String (Int32.to_string x)

  let of_yojson : Yojson.Safe.t -> (t, string) Result.t = function
    | `String s ->
        Ok (Int32.of_string s)
    | _ ->
        Error "bad uint64 string"

  let of_int x = Option.value_exn (Int32.of_int x)

  let of_string = Int32.of_string

  let to_bits x = List.init 32 ~f:(fun i -> Int32.((x lsr i) land one = one))
end

module Amount = Currency
module Fee = Currency
module Global_slot = UInt32
module Token_id = UInt64
module Nonce = UInt32

module Memo : sig
  type t [@@deriving yojson]

  val of_string : string -> t

  val to_bits : t -> bool list
end = struct
  let version_byte = '\x14'

  let length = 34

  let to_base58_check t = Base58_check.Encoding.encode ~version_byte t

  let of_base58_check s =
    let decoded = Base58_check.Encoding.decode_exn s ~version_byte in
    decoded

  type t = string

  let to_yojson x = `String (to_base58_check x)

  let of_yojson : Yojson.Safe.t -> _ = function
    | `String s ->
        Ok (of_base58_check s)
    | _ ->
        Error "bad public key"

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
  module Enum = struct
    type t = string [@@deriving yojson]
  end

  type t = bool * bool * bool [@@deriving yojson]

  let to_enum : t -> Enum.t = function
    | false, false, false ->
        "Payment"
    | _ ->
        failwith "to_enum"

  let of_enum : Enum.t -> t = function
    | "Payment" ->
        (false, false, false)
    | _ ->
        failwith "to_enum"

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

  module Json_payment = struct
    type inner =
      { source_pk: Public_key.Compressed.t
      ; receiver_pk: Public_key.Compressed.t
      ; token_id: Token_id.t
      ; amount: Amount.t }
    [@@deriving yojson]

    type t = Tag.Enum.t * inner [@@deriving yojson]
  end

  module Body = struct
    type t =
      { tag: Tag.t
      ; source_pk: Public_key.Compressed.t
      ; receiver_pk: Public_key.Compressed.t
      ; token_id: Token_id.t
      ; amount: Amount.t
      ; token_locked: bool }

    let to_yojson {tag; source_pk; receiver_pk; token_id; amount; token_locked}
        =
      assert (not token_locked) ;
      Json_payment.to_yojson
        ( Tag.to_enum tag
        , {Json_payment.source_pk; receiver_pk; token_id; amount} )

    let of_yojson j =
      Result.map (Json_payment.of_yojson j)
        ~f:(fun (tag, {Json_payment.source_pk; receiver_pk; token_id; amount})
           ->
          { tag= Tag.of_enum tag
          ; source_pk
          ; receiver_pk
          ; token_id
          ; amount
          ; token_locked= false } )
  end

  type t = {common: Common.t; body: Body.t} [@@deriving yojson]

  let to_input
      { common= {fee; fee_token; fee_payer_pk; nonce; valid_until; memo}
      ; body= {tag; source_pk; receiver_pk; token_id; amount; token_locked} } =
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
         ; Amount.to_bits amount
         ; [token_locked] |] }
end
