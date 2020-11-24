let (==) = `Don't_use_polymorphic_compare;

module Make =
       (
         N: {
           type t;

           let test_bit: (t, int) => bool;

           let num_bits: t => int;
         },
         Fq: {
           [@deriving (bin_io, sexp, eq, yojson)]
           type t;

           let zero: t;

           let one: t;

           let inv: t => t;

           let ( * ): (t, t) => t;

           let square: t => t;

           let negate: t => t;

           let (-): (t, t) => t;

           let (+): (t, t) => t;
         },
         Coefficients: {
           let a: Fq.t;

           let b: Fq.t;
         },
       ) => {
  [@deriving (bin_io, sexp, yojson)]
  type t = {
    x: Fq.t,
    y: Fq.t,
    z: Fq.t,
  };

  let zero = {x: Fq.zero, y: Fq.one, z: Fq.zero};

  module Coefficients = Coefficients;

  module Affine = {
    type t = (Fq.t, Fq.t);
  };

  let of_affine = ((x, y)) => {x, y, z: Fq.one};

  let is_zero = t => Fq.(equal(zero, t.x)) && Fq.(equal(zero, t.z));

  let to_affine_exn = ({x, y, z}) => {
    let z_inv = Fq.inv(z);
    Fq.(x * z_inv, y * z_inv);
  };

  let to_affine = t =>
    if (is_zero(t)) {
      None;
    } else {
      Some(to_affine_exn(t));
    };

  let is_well_formed = ({x, y, z} as t) =>
    if (is_zero(t)) {
      true;
    } else {
      open Fq;
      let x2 = square(x);
      let y2 = square(y);
      let z2 = square(z);
      equal(z * (y2 - Coefficients.b * z2), x * (x2 + Coefficients.a * z2));
    };

  let (+) = (t1, t2) =>
    if (is_zero(t1)) {
      t2;
    } else if (is_zero(t2)) {
      t1;
    } else {
      open Fq;
      let x1z2 = t1.x * t2.z;
      let x2z1 = t1.z * t2.x;
      let y1z2 = t1.y * t2.z;
      let y2z1 = t1.z * t2.y;
      if (equal(x1z2, x2z1) && equal(y1z2, y2z1)) {
        /* Double case */
        let xx = square(t1.x);
        let zz = square(t1.z);
        let w = Coefficients.a * zz + (xx + xx + xx);
        let y1z1 = t1.y * t1.z;
        let s = y1z1 + y1z1;
        let ss = square(s);
        let sss = s * ss;
        let r = t1.y * s;
        let rr = square(r);
        let b = square(t1.x + r) - xx - rr;
        let h = square(w) - (b + b);
        let x3 = h * s;
        let y3 = w * (b - h) - (rr + rr);
        let z3 = sss;
        {x: x3, y: y3, z: z3};
      } else {
        /* Generic case */
        let z1z2 = t1.z * t2.z;
        let u = y2z1 - y1z2;
        let uu = square(u);
        let v = x2z1 - x1z2;
        let vv = square(v);
        let vvv = v * vv;
        let r = vv * x1z2;
        let a = uu * z1z2 - (vvv + r + r);
        let x3 = v * a;
        let y3 = u * (r - a) - vvv * y1z2;
        let z3 = vvv * z1z2;
        {x: x3, y: y3, z: z3};
      };
    };

  let scale = (base, s) => {
    let rec go = (found_one, acc, i) =>
      if (i < 0) {
        acc;
      } else {
        let acc =
          if (found_one) {
            acc + acc;
          } else {
            acc;
          };
        if (N.test_bit(s, i)) {
          go(true, acc + base, i - 1);
        } else {
          go(found_one, acc, i - 1);
        };
      };

    go(false, zero, N.num_bits(s) - 1);
  };

  let ( * ) = (s, g) => scale(g, s);

  let negate = ({x, y, z}) => {x, y: Fq.negate(y), z};

  let (-) = (t1, t2) => t1 + negate(t2);
};
