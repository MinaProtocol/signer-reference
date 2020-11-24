open Core_kernel;

[@deriving sexp]
type t('field, 'bool) = {
  field_elements: array('field),
  bitstrings: array(list('bool)),
};

let append = (t1, t2) => {
  field_elements: Array.append(t1.field_elements, t2.field_elements),
  bitstrings: Array.append(t1.bitstrings, t2.bitstrings),
};

let field_elements = x => {field_elements: x, bitstrings: [||]};

let field = x => {field_elements: [|x|], bitstrings: [||]};

let bitstring = x => {field_elements: [||], bitstrings: [|x|]};

let bitstrings = x => {field_elements: [||], bitstrings: x};

let pack_to_fields = (~size_in_bits, ~pack, {field_elements, bitstrings}) => {
  let max_size = size_in_bits - 1;
  let rec pack_full_fields = (rev_fields, bits, length) =>
    if (length >= max_size) {
      let (field_bits, bits) = List.split_n(bits, max_size);
      pack_full_fields(
        [pack(field_bits), ...rev_fields],
        bits,
        length - max_size,
      );
    } else {
      (rev_fields, bits, length);
    };

  let packed_bits = {
    let (packed_field_elements, remaining_bits, remaining_length) =
      Array.fold(
        bitstrings,
        ~init=([], [], 0),
        ~f=((acc, bits, n), bitstring) => {
          let n = n + List.length(bitstring);
          let bits = bits @ bitstring;
          let (acc, bits, n) = pack_full_fields(acc, bits, n);
          (acc, bits, n);
        },
      );

    if (remaining_length == 0) {
      packed_field_elements;
    } else {
      [pack(remaining_bits), ...packed_field_elements];
    };
  };

  Array.append(field_elements, Array.of_list_rev(packed_bits));
};

let pack =
  pack_to_fields(
    ~size_in_bits=Base_field.length_in_bits,
    ~pack=Base_field.project_bits,
  );

let to_bits = (~unpack, {field_elements, bitstrings}) => {
  let field_bits = Array.map(~f=unpack, field_elements);
  List.concat @@ Array.to_list @@ Array.append(field_bits, bitstrings);
};
