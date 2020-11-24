open Core_kernel;

module Extended_projective = {
  [@deriving sexp]
  type t('a) = {
    x: 'a,
    y: 'a,
    z: 'a,
    t: 'a,
  };
};

module type Simple_elliptic_curve_intf = {
  type base;

  type t;

  module Affine: {type t = (base, base);};

  let to_affine_exn: t => Affine.t;

  let to_affine: t => option(Affine.t);
};

module type S = {
  module G1: {type t;};

  module G2: {type t;};

  module Fq_target: {type t;};

  module G1_precomputation: {
    [@deriving (bin_io, sexp)]
    type t;

    let create: G1.t => t;
  };

  module G2_precomputation: {
    [@deriving (bin_io, sexp)]
    type t;

    let create: G2.t => t;
  };

  let final_exponentiation: Fq_target.t => Fq_target.t;

  let miller_loop: (G1_precomputation.t, G2_precomputation.t) => Fq_target.t;

  let unreduced_pairing: (G1.t, G2.t) => Fq_target.t;

  let reduced_pairing: (G1.t, G2.t) => Fq_target.t;
};

module Make =
       (
         Fq: Fields.Fp_intf,
         Fq_twist: Fields.Extension_intf with type base = Fq.t,
         Fq_target: {
           include Fields.Degree_2_extension_intf with type base = Fq_twist.t;

           let frobenius: (t, int) => t;

           let cyclotomic_exp: (t, Fq.Nat.t) => t;
         },
         G1: Simple_elliptic_curve_intf with type base := Fq.t,
         G2: {
           include Simple_elliptic_curve_intf with type base := Fq_twist.t;

           module Coefficients: {let a: Fq_twist.t;};
         },
         Info: {
           let twist: Fq_twist.t;

           let loop_count: Fq.Nat.t;

           let is_loop_count_neg: bool;

           let final_exponent_last_chunk_w1: Fq.Nat.t;

           let final_exponent_last_chunk_is_w0_neg: bool;

           let final_exponent_last_chunk_abs_of_w0: Fq.Nat.t;
         },
       )

         : (
           S with
             module G1 := G1 and
             module G2 := G2 and
             module Fq_target := Fq_target
       ) => {
  module G1_precomputation = {
    [@deriving (bin_io, sexp)]
    type t_ = {
      px: Fq.t,
      py: Fq.t,
      px_twist: Fq_twist.t,
      py_twist: Fq_twist.t,
    };

    [@deriving (bin_io, sexp)]
    type t = option(t_);

    let create = (p: G1.t) =>
      Option.map(G1.to_affine(p), ~f=((px, py)) =>
        {
          px,
          py,
          px_twist: Fq_twist.scale(Info.twist, px),
          py_twist: Fq_twist.scale(Info.twist, py),
        }
      );
  };

  module Dbl_coeffs = {
    [@deriving (bin_io, sexp)]
    type t = {
      c_H: Fq_twist.t,
      c_4C: Fq_twist.t,
      c_J: Fq_twist.t,
      c_L: Fq_twist.t,
    };
  };

  module Add_coeffs = {
    [@deriving (bin_io, sexp)]
    type t = {
      c_L1: Fq_twist.t,
      c_RZ: Fq_twist.t,
    };
  };

  let loop_count_size_in_bits = Fq.Nat.num_bits(Info.loop_count);

  module G2_precomputation = {
    [@deriving (bin_io, sexp)]
    type t_ = {
      qx: Fq_twist.t,
      qy: Fq_twist.t,
      qy2: Fq_twist.t,
      qx_over_twist: Fq_twist.t,
      qy_over_twist: Fq_twist.t,
      dbl_coeffs: array(Dbl_coeffs.t),
      add_coeffs: array(Add_coeffs.t),
    };

    [@deriving (bin_io, sexp)]
    type t = option(t_);

    let twist_inv = Fq_twist.inv(Info.twist);

    let doubling_step_for_flipped_miller_loop =
        ({Extended_projective.x, y, z: _, t} as current) => {
      let a = Fq_twist.square(t);
      let b = Fq_twist.square(x);
      let c = Fq_twist.square(y);
      let d = Fq_twist.square(c);
      let e = Fq_twist.(square(x + c) - b - d);
      let f = Fq_twist.(b + b + b + G2.Coefficients.a * a);
      let g = Fq_twist.square(f);
      let next = {
        let x = Fq_twist.(negate(e + e + e + e) + g);
        let y =
          Fq_twist.(scale(d, Fq.(negate(of_int(8)))) + f * (e + e - x));

        let z =
          Fq_twist.(square(current.y + current.z) - c - square(current.z));

        let t = Fq_twist.square(z);
        {Extended_projective.x, y, z, t};
      };

      let coeffs = {
        Dbl_coeffs.c_H: Fq_twist.(square(next.z + current.t) - next.t - a),
        c_4C: Fq_twist.(c + c + c + c),
        c_J: Fq_twist.(square(f + t) - g - a),
        c_L: Fq_twist.(square(f + current.x) - g - b),
      };

      (next, coeffs);
    };

    let mixed_addition_step_for_flipped_miller_loop =
        (
          base_x,
          base_y,
          base_y_squared,
          {Extended_projective.x: x1, y: y1, z: z1, t: t1},
        ) => {
      open Fq_twist;
      let b = base_x * t1;
      let d = (square(base_y + z1) - base_y_squared - t1) * t1;
      let h = b - x1;
      let i = Fq_twist.square(h);
      let e = i + i + i + i;
      let j = h * e;
      let v = x1 * e;
      let l1 = d - (y1 + y1);
      let next = {
        let x = square(l1) - j - (v + v);
        let y = l1 * (v - x) - (y1 + y1) * j;
        let z = square(z1 + h) - t1 - i;
        let t = square(z);
        {Extended_projective.x, y, z, t};
      };

      (next, {Add_coeffs.c_L1: l1, c_RZ: next.z});
    };

    let create = (q: G2.t) => {
      open Option.Let_syntax;
      let%map (qx, qy) = G2.to_affine(q);
      let qy2 = Fq_twist.square(qy);
      let qx_over_twist = Fq_twist.(qx * twist_inv);
      let qy_over_twist = Fq_twist.(qy * twist_inv);
      let rec go = (found_one, r, dbl_coeffs, add_coeffs, i) =>
        if (i < 0) {
          (r, dbl_coeffs, add_coeffs);
        } else {
          let bit = Fq.Nat.test_bit(Info.loop_count, i);
          if (!found_one) {
            go(found_one || bit, r, dbl_coeffs, add_coeffs, i - 1);
          } else {
            let (r, dc) = doubling_step_for_flipped_miller_loop(r);
            let dbl_coeffs = [dc, ...dbl_coeffs];
            if (bit) {
              let (r, ac) =
                mixed_addition_step_for_flipped_miller_loop(qx, qy, qy2, r);

              let add_coeffs = [ac, ...add_coeffs];
              go(found_one, r, dbl_coeffs, add_coeffs, i - 1);
            } else {
              go(found_one, r, dbl_coeffs, add_coeffs, i - 1);
            };
          };
        };

      let (r, dbl_coeffs, add_coeffs) =
        go(
          false,
          {x: qx, y: qy, z: Fq_twist.one, t: Fq_twist.one},
          [],
          [],
          loop_count_size_in_bits - 1,
        );

      let add_coeffs =
        if (!Info.is_loop_count_neg) {
          add_coeffs;
        } else {
          open Fq_twist;
          let rZ_inv = inv(r.z);
          let rZ2_inv = square(rZ_inv);
          let rZ3_inv = rZ2_inv * rZ_inv;
          let minus_R_affine_X = r.x * rZ2_inv;
          let minus_R_affine_Y = negate(r.y) * rZ3_inv;
          let minus_R_affine_Y2 = square(minus_R_affine_Y);
          let (_r, ac) =
            mixed_addition_step_for_flipped_miller_loop(
              minus_R_affine_X,
              minus_R_affine_Y,
              minus_R_affine_Y2,
              r,
            );

          [ac, ...add_coeffs];
        };

      {
        qx,
        qy,
        qy2,
        qx_over_twist,
        qy_over_twist,
        dbl_coeffs: Array.of_list(List.rev(dbl_coeffs)),
        add_coeffs: Array.of_list(List.rev(add_coeffs)),
      };
    };
  };

  let miller_loop = (p: G1_precomputation.t, q: G2_precomputation.t) => {
    open Option.Let_syntax;
    let%map p = p
    and q = q;
    let l1_coeff = Fq_twist.(of_base(p.px) - q.qx_over_twist);
    let f = ref(Fq_target.one);
    let found_one = ref(false);
    let dbl_idx_r = ref(0);
    let add_idx_r = ref(0);
    for (i in loop_count_size_in_bits - 1 downto 0) {
      let bit = Fq.Nat.test_bit(Info.loop_count, i);
      if (! found_one^) {
        found_one := found_one^ || bit;
      } else {
        let dbl_idx = dbl_idx_r^;
        incr(dbl_idx_r);
        let dc = q.dbl_coeffs[dbl_idx];
        let g_RR_at_P: Fq_target.t = (
          Fq_twist.(
            negate(dc.c_4C) - dc.c_J * p.px_twist + dc.c_L,
            dc.c_H * p.py_twist,
          ): Fq_target.t
        );

        f := Fq_target.(square(f^) * g_RR_at_P);
        if (bit) {
          let add_idx = add_idx_r^;
          incr(add_idx_r);
          let ac = q.add_coeffs[add_idx];
          let g_RQ_at_P =
            Fq_twist.(
              ac.c_RZ * p.py_twist,
              negate(q.qy_over_twist * ac.c_RZ + l1_coeff * ac.c_L1),
            );

          f := Fq_target.(f^ * g_RQ_at_P);
        };
      };
    };
    if (Info.is_loop_count_neg) {
      let add_idx = add_idx_r^;
      incr(add_idx_r);
      let ac = q.add_coeffs[add_idx];
      let g_RnegR_at_P =
        Fq_twist.(
          ac.c_RZ * p.py_twist,
          negate(q.qy_over_twist * ac.c_RZ + l1_coeff * ac.c_L1),
        );

      f := Fq_target.(inv(f^ * g_RnegR_at_P));
    };
    f^;
  };

  let miller_loop = (p, q) =>
    /* The none case here means either p or q was the identity, so
       the pairing should evaluate to "zero" (i.e., one) in the
       target group. */
    switch (miller_loop(p, q)) {
    | None => Fq_target.one
    | Some(x) => x
    };

  let unreduced_pairing = (p, q) =>
    miller_loop(G1_precomputation.create(p), G2_precomputation.create(q));

  let final_exponentiation_first_chunk = (elt, elt_inv) => {
    open Fq_target;
    let elt_q3 = frobenius(elt, 3);
    let elt_q3_over_elt = elt_q3 * elt_inv;
    let alpha = frobenius(elt_q3_over_elt, 1);
    alpha * elt_q3_over_elt;
  };

  let final_exponentiation_last_chunk = (elt, elt_inv) => {
    open Fq_target;
    let elt_q = frobenius(elt, 1);
    let w1_part = cyclotomic_exp(elt_q, Info.final_exponent_last_chunk_w1);
    let w0_part =
      if (Info.final_exponent_last_chunk_is_w0_neg) {
        cyclotomic_exp(elt_inv, Info.final_exponent_last_chunk_abs_of_w0);
      } else {
        cyclotomic_exp(elt, Info.final_exponent_last_chunk_abs_of_w0);
      };

    w1_part * w0_part;
  };

  let final_exponentiation = x => {
    let x_inv = Fq_target.inv(x);
    let x_to_first_chunk = final_exponentiation_first_chunk(x, x_inv);
    let x_inv_to_first_chunk = final_exponentiation_first_chunk(x_inv, x);
    final_exponentiation_last_chunk(x_to_first_chunk, x_inv_to_first_chunk);
  };

  let reduced_pairing = (p, q) =>
    final_exponentiation(unreduced_pairing(p, q));
};
