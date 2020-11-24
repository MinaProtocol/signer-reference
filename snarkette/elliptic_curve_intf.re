module type S = {
  type field;

  type t;

  module Coefficients: {
    let a: field;

    let b: field;
  };

  module Affine: {type t = (field, field);};

  let (+): (t, t) => t;

  let to_affine_exn: t => (field, field);

  let to_affine: t => option((field, field));
};
