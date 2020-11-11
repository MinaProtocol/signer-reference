open Core_kernel

let lead = "\001\001"

module Encoding = struct
  let version_len = 1

  let checksum_len = 4

  let compute_checksum ~version_string payload =
    (* double-hash using SHA256 *)
    let open Digestif.SHA256 in
    let ctx0 = init () in
    let ctx1 = feed_string ctx0 version_string in
    let ctx2 = feed_string ctx1 payload in
    let first_hash = get ctx2 |> to_raw_string in
    let ctx3 = feed_string ctx0 first_hash in
    let second_hash = get ctx3 |> to_raw_string in
    second_hash |> String.sub ~pos:0 ~len:checksum_len

  (* same as Bitcoin alphabet *)
  let coda_alphabet =
    B58.make_alphabet
      "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"

  let encode ~version_byte payload =
    let version_string = String.make 1 version_byte in
    let checksum = compute_checksum payload ~version_string in
    let bytes = version_string ^ payload ^ checksum |> Bytes.of_string in
    B58.encode coda_alphabet bytes |> Bytes.to_string

  let decode_exn ~version_byte s =
    let version_string = String.make 1 version_byte in
    let bytes = Bytes.of_string s in
    let fail () = failwith "invalid base58" in
    let decoded =
      try B58.decode coda_alphabet bytes |> Bytes.to_string
      with B58.Invalid_base58_character -> fail ()
    in
    let len = String.length decoded in
    (* input must be at least as long as the version byte and checksum *)
    if len < version_len + checksum_len then fail () ;
    let checksum =
      String.sub decoded
        ~pos:(String.length decoded - checksum_len)
        ~len:checksum_len
    in
    let payload =
      String.sub decoded ~pos:1 ~len:(len - version_len - checksum_len)
    in
    if not (String.equal checksum (compute_checksum ~version_string payload))
    then fail () ;
    if not (Char.equal decoded.[0] version_byte) then fail () ;
    payload
end

let to_base58_check ~version_byte m t =
  Encoding.encode ~version_byte (lead ^ Binable.to_string m t)

let of_base58_check ~version_byte m s =
  let decoded = Encoding.decode_exn s ~version_byte in
  Binable.of_string m
    (String.chop_prefix decoded ~prefix:lead |> Option.value_exn)
