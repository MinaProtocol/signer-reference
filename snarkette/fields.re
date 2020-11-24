open Core_kernel;
open Fold_lib;
open Tuple_lib;

let (==) = `Don't_use_polymorphic_equality;

module type Basic_intf = {
  module Nat: Nat_intf.S;

  [@deriving eq]
  type t;

  let order: Nat.t;

  let one: t;

  let zero: t;

  let (+): (t, t) => t;

  let ( * ): (t, t) => t;

  let (-): (t, t) => t;

  let (/): (t, t) => t;

  let square: t => t;
};

module type Intf = {
  [@deriving (bin_io, sexp, yojson, compare, hash)]
  type t;

  include Basic_intf with type t := t;

  let gen: Quickcheck.Generator.t(t);

  let gen_incl: (t, t) => Quickcheck.Generator.t(t);

  let gen_uniform: Quickcheck.Generator.t(t);

  let gen_uniform_incl: (t, t) => Quickcheck.Generator.t(t);

  let random: unit => t;

  let negate: t => t;

  let inv: t => t;

  let parity: t => bool;
};

module type Sqrt_field_intf = {
  include Intf;

  let is_square: t => bool;

  let sqrt: t => t;
};

module type Extended_intf = {
  include Sqrt_field_intf;

  let ( ** ): (t, Nat.t) => t;
};

module type Fp_intf = {
  include Intf;

  include Stringable.S with type t := t;

  include Stringable.S with type t := t;

  let of_int: int => t;

  let of_bits: list(bool) => option(t);

  let to_bigint: t => Nat.t;

  let of_bigint: Nat.t => t;

  let fold_bits: t => Fold.t(bool);

  let fold: t => Fold.t(Triple.t(bool));

  let to_bits: t => list(bool);

  let length_in_bits: int;

  let is_square: t => bool;

  let sqrt: t => t;
};

module type Extension_intf = {
  type base;

  include Extended_intf;

  let scale: (t, base) => t;

  let of_base: base => t;

  let project_to_base: t => base;

  let to_list: t => list(base);
};

module Extend = (F: Basic_intf) => {
  open F;

  let ( ** ) = (x, n) => {
    let k = Nat.num_bits(n);
    let rec go = (acc, i) =>
      if (Int.(i < 0)) {
        acc;
      } else {
        let acc = square(acc);
        let acc =
          if (Nat.test_bit(n, i)) {
            acc * x;
          } else {
            acc;
          };
        go(acc, Int.(i - 1));
      };

    go(one, Int.(k - 1));
  };

  let is_square = {
    let euler = Nat.((order - of_int(1)) /\/ of_int(2));
    x => equal(x ** euler, one);
  };

  module Sqrt_params = {
    let two_adicity = n => {
      let rec go = i =>
        if (Nat.test_bit(n, i)) {
          i;
        } else {
          go(Int.(i + 1));
        };
      go(0);
    };

    type nonrec t = {
      two_adicity: int,
      quadratic_non_residue_to_t: t,
      t_minus_1_over_2: Nat.t,
    };

    let first = f => {
      let rec go = i =>
        switch (f(i)) {
        | Some(x) => x
        | None => go(i + one)
        };
      go(one);
    };

    let create = () => {
      let p_minus_one = Nat.(order - of_int(1));
      let s = two_adicity(p_minus_one);
      let t = Nat.shift_right(p_minus_one, s);
      let quadratic_non_residue =
        first(i => Option.some_if(!is_square(i), i));

      {
        two_adicity: s,
        quadratic_non_residue_to_t: quadratic_non_residue ** t,
        t_minus_1_over_2: Nat.((t - of_int(1)) /\/ of_int(2)),
      };
    };

    let t = lazy(create());
  };

  let rec loop = (~while_, ~init, f) =>
    if (while_(init)) {
      loop(~while_, ~init=f(init), f);
    } else {
      init;
    };

  let rec pow2 = (b, n) =>
    if (n > 0) {
      pow2(square(b), Int.(n - 1));
    } else {
      b;
    };

  let sqrt = {
    let pow2_order = b =>
      loop(
        ~while_=((b2m, _)) => !equal(b2m, one),
        ~init=(b, 0),
        ((b2m, m)) => (square(b2m), Int.succ(m)),
      )
      |> snd;

    module Loop_params = {
      type nonrec t = {
        z: t,
        b: t,
        x: t,
        v: int,
      };
    };
    Loop_params.(
      a => {
        let {
          Sqrt_params.two_adicity: v,
          quadratic_non_residue_to_t: z,
          t_minus_1_over_2,
        } =
          Lazy.force(Sqrt_params.t);

        let w = a ** t_minus_1_over_2;
        let x = a * w;
        let b = x * w;
        let {x, _} =
          loop(
            ~while_=p => !equal(p.b, one),
            ~init={z, b, x, v},
            ({z, b, x, v}) => {
              let m = pow2_order(b);
              let w = pow2(z, Int.(v - m - 1));
              let z = square(w);
              {z, b: b * z, x: x * w, v: m};
            },
          );

        x;
      }
    );
  };
};

module Make_fp =
       (N: Nat_intf.S, Info: {let order: N.t;})
       : (Fp_intf with module Nat = N and type t = pri N.t) => {
  include Info;

  module T = {
    let zero = N.of_int(0);

    let one = N.of_int(1);

    let length_in_bits = N.num_bits(N.(Info.order - one));

    module Nat = N;
    open Nat;

    let order = Info.order;

    /* TODO version */
    [@deriving (eq, sexp, yojson, compare, hash)]
    type t = N.t;

    let length_in_bytes = Int.((length_in_bits + 7) / 8);

    /** serialization meant to be identical to field serializations in snarky */
    include Bin_prot.Utils.Of_minimal({
      type nonrec t = t;

      let bin_shape_t =
        Bin_prot.Shape.basetype(
          Bin_prot.Shape.Uuid.of_string(
            sprintf("snarkette_field_%d", length_in_bytes),
          ),
          [],
        );

      let __bin_read_t__ = (_buf, ~pos_ref, _vint) =>
        Bin_prot.Common.raise_variant_wrong_type("Fp.t", pos_ref^);

      let bin_size_t = _ => length_in_bytes;

      let bin_write_t = (buf, ~pos, t) => {
        let bs = Bigstring.of_string(N.to_bytes(t));
        let n = Bigstring.length(bs);
        Bigstring.blit(~src=bs, ~dst=buf, ~src_pos=0, ~dst_pos=pos, ~len=n);
        if (Int.(n < length_in_bytes)) {
          for (i in n to Int.(length_in_bytes - 1)) {
            Bigstring.set(buf, Int.(pos + i), '\000');
          };
        };
        Int.(pos + length_in_bytes);
      };

      let bin_read_t = (buf, ~pos_ref) => {
        open Int;
        let remaining_bytes = Bigstring.length(buf) - pos_ref^;
        if (remaining_bytes < length_in_bytes) {
          failwithf(
            "Field.bin_read_t: Expected %d bytes, got %d",
            length_in_bytes,
            remaining_bytes,
            (),
          );
        };
        let t =
          N.of_bytes(
            Bigstring.to_string(buf, ~pos=pos_ref^, ~len=length_in_bytes),
          );

        pos_ref := length_in_bytes + pos_ref^;
        t;
      };
    });

    let (+) = (x, y) => (x + y) % Info.order;

    let (-) = (x, y) => (x - y) % Info.order;

    let ( * ) = (x, y) => x * y % Info.order;

    let square = x => x * x;

    let rec extended_euclidean = (a, b) =>
      if (equal(b, zero)) {
        (a, one, zero);
      } else {
        switch (extended_euclidean(b, a % b)) {
        | (d, x, y) => (d, y, x - a /\/ b * y)
        };
      };

    let inv_no_mod = x => {
      let (_, a, _b) = extended_euclidean(x, Info.order);
      a;
    };

    let inv = x => inv_no_mod(x) % Info.order;

    let (/) = (x, y) => x * inv_no_mod(y);
  };

  include Extend(T);
  include T;

  let of_bigint = x => N.(x % Info.order);

  let to_bigint = Fn.id;

  let parity = t => N.test_bit(to_bigint(t), 0);

  let make_gen = (gen, lo, hi) => {
    let t_of_bignum_bigint = n => Bigint.to_string(n) |> N.of_string;
    Quickcheck.Generator.map(gen(lo, hi), ~f=t_of_bignum_bigint);
  };

  /* fix zero, size - 1 bounds */
  let make_gen_full = gen => {
    let size = order |> N.to_string |> Bigint.of_string;
    make_gen(gen, Bigint.zero, Bigint.(size - one));
  };

  let gen = make_gen_full(Bigint.gen_incl);

  let gen_incl = (lo, hi) => {
    let bignum_bigint_of_t = t => N.to_string(t) |> Bigint.of_string;
    make_gen(
      Bigint.gen_incl,
      bignum_bigint_of_t(lo),
      bignum_bigint_of_t(hi),
    );
  };

  let gen_uniform = make_gen_full(Bigint.gen_uniform_incl);

  let gen_uniform_incl = (lo, hi) => {
    let bignum_bigint_of_t = t => N.to_string(t) |> Bigint.of_string;
    make_gen(
      Bigint.gen_uniform_incl,
      bignum_bigint_of_t(lo),
      bignum_bigint_of_t(hi),
    );
  };

  let random = () => Quickcheck.random_value(gen_uniform);

  let fold_bits = (n): Fold_lib.Fold.t(bool) => {
    fold: (~init, ~f) => {
      let rec go = (acc, i) =>
        if (Int.(i == length_in_bits)) {
          acc;
        } else {
          go(f(acc, N.test_bit(n, i)), Int.(i + 1));
        };

      go(init, 0);
    },
  };

  let to_bits = Fn.compose(Fold_lib.Fold.to_list, fold_bits);

  let fold = n => Fold_lib.Fold.group3(~default=false, fold_bits(n));

  let of_bits = bits => {
    let rec go = (acc, i) =>
      fun
      | [] => acc
      | [b, ...bs] => {
          let acc =
            if (b) {
              N.log_or(acc, N.shift_left(one, i));
            } else {
              acc;
            };
          go(acc, Int.(i + 1), bs);
        };

    let r = go(zero, 0, bits);
    if (N.(<)(r, Info.order)) {
      Some(r);
    } else {
      None;
    };
  };

  open N;

  let of_int = N.of_int;

  let of_string = N.of_string;

  let to_string = N.to_string;

  let negate = x => N.(-)(Info.order, x);

  let%test_unit "exp test" =
    [%test_eq: t](of_int(8), of_int(2) ** of_int(3));

  let%test_unit "pow2" = {
    let b = 7;
    if (N.(of_int(Int.(7 ** 8)) < order)) {
      [%test_eq: t](pow2(of_int(b), 3), of_int(Int.(7 ** 8)));
    } else {
      ();
    };
  };

  let%test_unit "sqrt agrees with integer square root on small values" = {
    let rec mem = a =>
      fun
      | [] => ()
      | [x, ...xs] =>
        try([%test_eq: t](a, x)) {
        | _ => mem(a, xs)
        };

    let gen = Int.gen_incl(1, Int.max_value_30_bits);
    Quickcheck.test(
      ~trials=10,
      gen,
      ~f=n => {
        let n = abs(n);
        let n2 = Int.(n * n);
        mem(sqrt(of_int(n2)), [of_int(n), Info.order - of_int(n)]);
      },
    );
  };
};

module type Degree_2_extension_intf = {
  type base;

  include Extension_intf with type base := base and type t = (base, base);
};

module type Degree_3_extension_intf = {
  type base;

  include
    Extension_intf with type base := base and type t = (base, base, base);
};

let (%) = (x, n) => {
  let r = x mod n;
  if (r < 0) {
    r + n;
  } else {
    r;
  };
};

let find_wnaf =
    (type t, module N: Nat_intf.S with type t = t, window_size, scalar) => {
  let one = N.of_int(1);
  let first_k_bits = (c, k) => {
    let k_bits = N.(shift_left(one, k) - one);
    N.to_int_exn(N.log_and(k_bits, c));
  };

  let length = N.num_bits(scalar);
  let res = Array.init(length + 1, ~f=_ => 0);
  let zero = N.of_int(0);
  let rec go = (c, j) =>
    if (N.equal(zero, c)) {
      ();
    } else {
      let (u, c) =
        if (N.test_bit(c, 0)) {
          let u = {
            let u = first_k_bits(c, window_size + 1);
            if (u > 1 lsl window_size) {
              u - 1 lsl (window_size + 1);
            } else {
              u;
            };
          };

          let c = N.(c - of_int(u));
          (u, c);
        } else {
          (0, c);
        };

      res[j] = u;
      go(N.shift_right(c, 1), j + 1);
    };

  go(scalar, 0);
  res;
};

module Make_fp3 =
       (
         Fp: Intf,
         Info: {
           let non_residue: Fp.t;

           let frobenius_coeffs_c1: array(Fp.t);

           let frobenius_coeffs_c2: array(Fp.t);
         },
       )
       : {
         include
           Degree_3_extension_intf with
             type base = Fp.t and module Nat = Fp.Nat;

         let non_residue: Fp.t;

         let frobenius: (t, int) => t;
       } => {
  include Info;

  type base = Fp.t;

  let componentwise = (f, (x1, x2, x3), (y1, y2, y3)) => (
    f(x1, y1),
    f(x2, y2),
    f(x3, y3),
  );

  let of_base = x => (x, Fp.zero, Fp.zero);

  module T = {
    module Nat = Fp.Nat;

    let order = Nat.(Fp.order * Fp.order * Fp.order);

    [@deriving (eq, bin_io, sexp, yojson, compare, hash)]
    type t = (Fp.t, Fp.t, Fp.t);

    let (+) = componentwise(Fp.(+));

    let (-) = componentwise(Fp.(-));

    let ( * ) = ((a1, b1, c1), (a2, b2, c2)) => {
      let a = Fp.(a1 * a2);
      let b = Fp.(b1 * b2);
      let c = Fp.(c1 * c2);
      Fp.(
        a + non_residue * ((b1 + c1) * (b2 + c2) - b - c),
        (a1 + b1) * (a2 + b2) - a - b + non_residue * c,
        (a1 + c1) * (a2 + c2) - a + b - c,
      );
    };

    let square = ((a, b, c)) => {
      let s0 = Fp.square(a);
      let ab = Fp.(a * b);
      let s1 = Fp.(ab + ab);
      let s2 = Fp.(square(a - b + c));
      let bc = Fp.(b * c);
      let s3 = Fp.(bc + bc);
      let s4 = Fp.square(c);
      Fp.(
        s0 + non_residue * s3,
        s1 + non_residue * s4,
        s1 + s2 + s3 - s0 - s4,
      );
    };

    let inv = ((a, b, c)) => {
      open Fp;
      let t0 = square(a);
      let t1 = square(b);
      let t2 = square(c);
      let t3 = a * b;
      let t4 = a * c;
      let t5 = b * c;
      let c0 = t0 - non_residue * t5;
      let c1 = non_residue * t2 - t3;
      let c2 = t1 - t4;
      let t6 = a * c0 + non_residue * (c * c1 + b * c2) |> inv;
      (t6 * c0, t6 * c1, t6 * c2);
    };

    let (/) = (x, y) => x * inv(y);

    let one = of_base(Fp.one);

    let zero = of_base(Fp.zero);
  };

  include T;
  include Extend(T);

  let gen = Quickcheck.Generator.tuple3(Fp.gen, Fp.gen, Fp.gen);

  let gen_incl = ((lo1, lo2, lo3), (hi1, hi2, hi3)) =>
    Quickcheck.Generator.tuple3(
      Fp.gen_incl(lo1, hi1),
      Fp.gen_incl(lo2, hi2),
      Fp.gen_incl(lo3, hi3),
    );

  let gen_uniform =
    Quickcheck.Generator.tuple3(
      Fp.gen_uniform,
      Fp.gen_uniform,
      Fp.gen_uniform,
    );

  let gen_uniform_incl = ((lo1, lo2, lo3), (hi1, hi2, hi3)) =>
    Quickcheck.Generator.tuple3(
      Fp.gen_uniform_incl(lo1, hi1),
      Fp.gen_uniform_incl(lo2, hi2),
      Fp.gen_uniform_incl(lo3, hi3),
    );

  let random = () => Quickcheck.random_value(gen_uniform);

  let to_list = ((x, y, z)) => [x, y, z];

  let project_to_base = ((x, _, _)) => x;

  let parity = Fn.compose(Fp.parity, project_to_base);

  let scale = ((x1, x2, x3), s) => Fp.(s * x1, s * x2, s * x3);

  let negate = ((x1, x2, x3)) => Fp.(negate(x1), negate(x2), negate(x3));

  let frobenius = ((c0, c1, c2), power) => {
    open Fp;
    open Info;
    let i = power mod 3;
    (c0, frobenius_coeffs_c1[i] * c1, frobenius_coeffs_c2[i] * c2);
  };
};

module Make_fp2 =
       (Fp: Intf, Info: {let non_residue: Fp.t;})
       : {
         include
           Degree_2_extension_intf with
             type base = Fp.t and module Nat = Fp.Nat;
       } => {
  type base = Fp.t;

  let of_base = x => (x, Fp.zero);

  let componentwise = (f, (x1, x2), (y1, y2)) => (f(x1, y1), f(x2, y2));

  module T = {
    [@deriving (eq, yojson, bin_io, sexp, compare, hash)]
    type t = (Fp.t, Fp.t);

    module Nat = Fp.Nat;

    let order = Nat.(Fp.order * Fp.order);

    let one = of_base(Fp.one);

    let zero = of_base(Fp.zero);

    let (+) = componentwise(Fp.(+));

    let (-) = componentwise(Fp.(-));

    let square = ((a, b)) => {
      open Info;
      let ab = Fp.(a * b);
      Fp.((a + b) * (a + non_residue * b) - ab - non_residue * ab, ab + ab);
    };

    let ( * ) = ((a1, b1), (a2, b2)) => {
      open Fp;
      let a = a1 * a2;
      let b = b1 * b2;
      (a + Info.non_residue * b, (a1 + b1) * (a2 + b2) - a - b);
    };

    let inv = ((a, b)) => {
      open Fp;
      let t0 = square(a);
      let t1 = square(b);
      let t2 = t0 - Info.non_residue * t1;
      let t3 = inv(t2);
      let c0 = a * t3;
      let c1 = negate(b * t3);
      (c0, c1);
    };

    let (/) = (x, y) => x * inv(y);
  };

  include T;
  include Extend(T);

  let gen = Quickcheck.Generator.tuple2(Fp.gen, Fp.gen);

  let gen_incl = ((lo1, lo2), (hi1, hi2)) =>
    Quickcheck.Generator.tuple2(
      Fp.gen_incl(lo1, hi1),
      Fp.gen_incl(lo2, hi2),
    );

  let gen_uniform =
    Quickcheck.Generator.tuple2(Fp.gen_uniform, Fp.gen_uniform);

  let gen_uniform_incl = ((lo1, lo2), (hi1, hi2)) =>
    Quickcheck.Generator.tuple2(
      Fp.gen_uniform_incl(lo1, hi1),
      Fp.gen_uniform_incl(lo2, hi2),
    );

  let random = () => Quickcheck.random_value(gen_uniform);

  let to_list = ((x, y)) => [x, y];

  let project_to_base = ((x, _)) => x;

  let parity = Fn.compose(Fp.parity, project_to_base);

  let scale = ((x1, x2), s) => Fp.(s * x1, s * x2);

  let negate = ((a, b)) => Fp.(negate(a), negate(b));
};

module Make_fp6 =
       (
         N: Nat_intf.S,
         Fp: Intf,
         Fp2: Degree_2_extension_intf with type base = Fp.t,
         Fp3: {
           include Degree_3_extension_intf with type base = Fp.t;

           let frobenius: (t, int) => t;

           let non_residue: Fp.t;
         },
         Info: {
           let non_residue: Fp.t;

           let frobenius_coeffs_c1: array(Fp.t);
         },
       )
       : {
         include
           Degree_2_extension_intf with
             type base = Fp3.t and module Nat = Fp.Nat;

         let mul_by_2345: (t, t) => t;

         let frobenius: (t, int) => t;

         let cyclotomic_exp: (t, N.t) => t;

         let unitary_inverse: t => t;
       } => {
  module T = {
    module Nat = Fp.Nat;

    let of_base = x => (x, Fp3.zero);

    let componentwise = (f, (x1, x2), (y1, y2)) => (
      f(x1, y1),
      f(x2, y2),
    );

    [@deriving (eq, yojson, bin_io, sexp, compare, hash)]
    type t = (Fp3.t, Fp3.t);

    let order = {
      open Nat;
      let square = x => x * x;
      let p = Fp.order;
      square(p * square(p));
    };

    let zero = of_base(Fp3.zero);

    let one = of_base(Fp3.one);

    let (+) = componentwise(Fp3.(+));

    let (-) = componentwise(Fp3.(-));

    let mul_by_non_residue = ((c0, c1, c2): Fp3.t) =>
      Fp.(Info.non_residue * c2, c0, c1);

    let square = ((a, b)) => {
      let ab = Fp3.(a * b);
      Fp3.(
        (a + b) * (a + mul_by_non_residue(b)) - ab - mul_by_non_residue(ab),
        ab + ab,
      );
    };

    let ( * ) = ((a1, b1), (a2, b2)) => {
      let a = Fp3.(a1 * a2);
      let b = Fp3.(b1 * b2);
      let beta_b = mul_by_non_residue(b);
      Fp3.(a + beta_b, (a1 + b1) * (a2 + b2) - a - b);
    };

    let inv = ((a, b)) => {
      let t1 = Fp3.square(b);
      let t0 = Fp3.(square(a) - mul_by_non_residue(t1));
      let new_t1 = Fp3.inv(t0);
      Fp3.(a * new_t1, negate(b * new_t1));
    };

    let (/) = (x, y) => x * inv(y);
  };

  include T;
  include Extend(T);

  type base = Fp3.t;

  let gen = Quickcheck.Generator.tuple2(Fp3.gen, Fp3.gen);

  let gen_incl = ((lo1, lo2), (hi1, hi2)) =>
    Quickcheck.Generator.tuple2(
      Fp3.gen_incl(lo1, hi1),
      Fp3.gen_incl(lo2, hi2),
    );

  let gen_uniform =
    Quickcheck.Generator.tuple2(Fp3.gen_uniform, Fp3.gen_uniform);

  let gen_uniform_incl = ((lo1, lo2), (hi1, hi2)) =>
    Quickcheck.Generator.tuple2(
      Fp3.gen_uniform_incl(lo1, hi1),
      Fp3.gen_uniform_incl(lo2, hi2),
    );

  let random = () => Quickcheck.random_value(gen_uniform);

  let to_list = ((x, y)) => [x, y];

  let project_to_base = ((x, _)) => x;

  let parity = Fn.compose(Fp3.parity, project_to_base);

  let scale = ((x1, x2), s) => Fp3.(s * x1, s * x2);

  let mul_by_2345 = ((a1, b1), (a2, b2)) => {
    open Info;
    let (a1_0, a1_1, a1_2) = a1;
    let (_, _, a2_2) = a2;
    {
      let (a2_0, a2_1, _) = a2;
      assert(Fp.(equal(a2_0, zero)));
      assert(Fp.(equal(a2_1, zero)));
    };
    let a =
      Fp.(a1_1 * a2_2 * non_residue, a1_2 * a2_2 * non_residue, a1_0 * a2_2);

    let b = Fp3.(b1 * b2);
    let beta_b = mul_by_non_residue(b);
    Fp3.(a + beta_b, (a1 + b2) * (a2 + b2) - a - b);
  };

  let negate = ((a, b)) => Fp3.(negate(a), negate(b));

  let unitary_inverse = ((x, y)) => (x, Fp3.negate(y));

  let cyclotomic_square = (((c00, c01, c02), (c10, c11, c12))) => {
    let a: Fp2.t = ((c00, c11): Fp2.t);
    let b: Fp2.t = ((c10, c02): Fp2.t);
    let c: Fp2.t = ((c01, c12): Fp2.t);
    let asq = Fp2.square(a);
    let bsq = Fp2.square(b);
    let csq = Fp2.square(c);
    let a_a = {
      open Fp;
      let a_a = fst(asq) - fst(a);
      a_a + a_a + fst(asq);
    };

    let a_b = {
      open Fp;
      let a_b = snd(asq) + snd(a);
      a_b + a_b + snd(asq);
    };

    let b_a = {
      open Fp;
      let b_tmp = Fp3.non_residue * snd(csq);
      let b_a = b_tmp + fst(b);
      b_a + b_a + b_tmp;
    };

    let b_b = {
      open Fp;
      let b_b = fst(csq) - snd(b);
      b_b + b_b + fst(csq);
    };

    let c_a = {
      open Fp;
      let c_a = fst(bsq) - fst(c);
      c_a + c_a + fst(bsq);
    };

    let c_b = {
      open Fp;
      let c_b = snd(bsq) + snd(c);
      c_b + c_b + snd(bsq);
    };

    ((a_a, c_a, b_b), (b_a, a_b, c_b));
  };

  let cyclotomic_exp = (x, exponent) => {
    let x_inv = inv(x);
    let naf = find_wnaf((module N), 1, exponent);
    let rec go = (found_nonzero, res, i) =>
      if (i < 0) {
        res;
      } else {
        let res =
          if (found_nonzero) {
            cyclotomic_square(res);
          } else {
            res;
          };
        if (naf[i] != 0) {
          let found_nonzero = true;
          let res =
            if (naf[i] > 0) {
              res * x;
            } else {
              res * x_inv;
            };
          go(found_nonzero, res, Int.(i - 1));
        } else {
          go(found_nonzero, res, Int.(i - 1));
        };
      };

    go(false, one, Int.(Array.length(naf) - 1));
  };

  let frobenius = ((c0, c1), power) => (
    Fp3.frobenius(c0, power),
    Fp3.(scale(frobenius(c1, power), Info.frobenius_coeffs_c1[power mod 6])),
  );
};
