open Core_kernel

(* 
  Define
  p = 2^254 + 4707489545178046908921067385359695873 = 28948022309329048855892746252171976963322203655955319056773317069363642105857
  q = 2^254 + 4707489544292117082687961190295928833 = 28948022309329048855892746252171976963322203655954433126947083963168578338817

  "Curve" is a module implementing the elliptic curve with defining equation

   y^2 = x^3 + 5

  defined over the field Fq of order q. This curve has scalar-field the field Fp of order p.
*)

module Field = Base_field

let initial_state =
  let prefix_to_field (s : string) =
    let bits_per_character = 8 in
    assert (bits_per_character * String.length s < Field.length_in_bits) ;
    Field.project_bits Fold_lib.Fold.(to_list (string_bits (s :> string)))
  in
  let s = "CodaSignature*******" in
  assert (String.length s = 20) ;
  Poseidon.hash_state
    ~init:[|Field.zero; Field.zero; Field.zero|]
    [|prefix_to_field s|]

module Curve = struct
  include Snarkette.Tweedle.Dee

  let scale (p : t) (x : Scalar_field.t) = scale p (Scalar_field.to_bigint x)
end

module Poseidon = Poseidon

module Private_key = struct
  (* An Fp element *)
  type t = Scalar_field.t
end

module Public_key = struct
  (* A point on the curve *)
  type t = Curve.t

  module Compressed = struct
    (* the x coordinate and y-parity of a curve point *)
    type t = {x: Field.t; is_odd: bool}
  end
end

module Signature = struct
  type t = Field.t * Scalar_field.t
end

module Message = struct
  (* A message is a "random oracle input", which is a struct containing
     - an array of field elements
     - an array of bitstrings.

     They are kept separate because we use an arithmetic hash function (Poseidon) which
     natively accepts arrays of field elements as inputs.

     When we actually need to hash such a value, we "pack" all the bitstrings
     into as few field elements as we can and then feed that to the hash function
     along with the array of field elements.
  *)
  type t = (Field.t, bool) Random_oracle_input.t

  (* The implementation of this function is not important and
   the verification procedure does not depend on it. This is
   here to avoid having to sample a random nonce when signing.

   Instead of sampling a random nonce, we hash together the
   private key, public key, and the message using a hash function
   which is modelled as a random oracle. Here we use blake2 but
   any hash function could be used. *)
  let derive t ~private_key ~public_key =
    let input =
      let x, y = Curve.to_affine_exn public_key in
      (* "append" works by concatenating the field element arrays
         and the bitstring arrays in the two "inputs" *)
      Random_oracle_input.append t
        { field_elements= [|x; y|]
        ; bitstrings= [|Scalar_field.to_bits private_key|] }
    in
    Random_oracle_input.to_bits ~unpack:Field.to_bits input
    |> Array.of_list |> Blake2.bits_to_string |> Blake2.digest_string
    |> Blake2.to_raw_string |> Blake2.string_to_bits |> Array.to_list
    |> Scalar_field.project_bits

  (* Hash the message together with the public key and [r], and use the output as the Schnorr challenge. *)
  let hash t ~public_key ~r =
    let input =
      let px, py = Curve.to_affine_exn public_key in
      Random_oracle_input.append t
        {field_elements= [|px; py; r|]; bitstrings= [||]}
    in
    (* "init" is the initial state vector of 3 Fq elements.
       it is equal to the hash state after consuming the string

       "CodaSignature*******"

       where the string is interpreted as a field element by converting
       it to bits (internal byte order being little endian) and then interpreting
       the resulting 160 bits as a little-endian representation of a field element.
    *)
    Poseidon.digest ~init:initial_state (Random_oracle_input.pack input)
    (* Poseidon returns an Fq element. We convert it to an Fp element by converting the Fq element to a little endian bit
   string and then converting that little endian bit string to an Fp element. *)
    |> Field.to_bits
    |> Scalar_field.project_bits
end

let is_even (t : Field.t) = not (Field.Nat.test_bit (Field.to_bigint t) 0)

let sign (d_prime : Private_key.t) m =
  let public_key = Curve.scale Curve.one d_prime in
  let d = d_prime in
  let k_prime = Message.derive m ~public_key ~private_key:d in
  assert (not Scalar_field.(equal k_prime zero)) ;
  let r, ry = Curve.(to_affine_exn (scale Curve.one k_prime)) in
  let k = if is_even ry then k_prime else Scalar_field.negate k_prime in
  let e = Message.hash m ~public_key ~r in
  let s = Scalar_field.(k + (e * d)) in
  (r, s)

let verify ((r, s) : Signature.t) (pk : Public_key.t) (m : Message.t) =
  let e = Message.hash ~public_key:pk ~r m in
  let r_pt = Curve.(scale one s + negate (scale pk e)) in
  match Curve.to_affine_exn r_pt with
  | rx, ry ->
      is_even ry && Field.equal rx r
  | exception _ ->
      false

(* A test *)
let () =
  let message =
    Random_oracle_input.field_elements
      [|Field.of_int 1; Field.of_int 2; Field.of_int 345|]
  in
  let privkey = Scalar_field.random () in
  let pubkey = Curve.scale Curve.one privkey in
  let signature = sign privkey message in
  assert (verify signature pubkey message) ;
  assert (
    not
      (verify signature pubkey
         (Random_oracle_input.field_elements [|Field.of_int 222|])) )

(* For signing transactions, we need to specify coda's transaction format and
   how transactions are converted into "random oracle input" structs

   A coda transaction has the structure

   { payload:
    { common:
        { fee: Fee.t
        , fee_token: Token_id.t
        , fee_payer_pk: Public_key.Compressed.t
        , nonce: Nonce.t
        , valid_until: Global_slot.t
        , memo: char[34] }
    , body:
        { tag: Tag.t
        , source_pk: Public_key.Compressed.t
        , receiver_pk: Public_key.Compressed.t
        , token_id: Token_id.t
        , amount: Amount.t }
    }
   , signer: Public_key.Compressed.t
   , signature: Signature.t
   }

   - Amount.t is a uint64
   - Fee.t is a uint64
   - Global_slot.t is a uint32
   - Token_id.t is a uint64
   - the tag is the three bits 000 for a payment and 001 for a stake delegation

   To sign this, we convert the "payload" field to an "random oracle input", i.e., an
   array of field elements and an array of bitstrings.

   The "inputs" struct this gets reduced to looks like
   { field_elements=[|
      fee_payer_pk.x,
      source_pk.x, receiver_pk.x
     |]
   , bitstrings= [|
      fee, fee_token, fee_payer_pk.is_odd, nonce, valid_until, memo,
      tag, [source_pk.is_odd], [receiver_pk.is_odd], token_id, amount
     |]
   }
*)
