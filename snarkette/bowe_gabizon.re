open Core_kernel;
open Fold_lib;

let (==) = `Don't_use_polymorphic_equality;

module type Backend_intf = {
  module N: Nat_intf.S;

  module Fq: Fields.Fp_intf with module Nat := N;

  module Fqe: Fields.Extension_intf with type base = Fq.t;

  module G1: {
    [@deriving (sexp, bin_io)]
    type t;

    let zero: t;

    let to_affine_exn: t => (Fq.t, Fq.t);

    let is_well_formed: t => bool;

    let ( * ): (N.t, t) => t;

    let (+): (t, t) => t;
  };

  module G2: {
    [@deriving (sexp, bin_io)]
    type t;

    let one: t;

    let to_affine_exn: t => (Fqe.t, Fqe.t);

    let (+): (t, t) => t;

    let is_well_formed: t => bool;
  };

  let hash:
    (
      ~message: array(Fq.t)=?,
      ~a: G1.t,
      ~b: G2.t,
      ~c: G1.t,
      ~delta_prime: G2.t
    ) =>
    G1.t;

  module Fq_target: {
    include Fields.Degree_2_extension_intf with type base = Fqe.t;

    let unitary_inverse: t => t;
  };

  module Pairing:
    Pairing.S with
      module G1 := G1 and module G2 := G2 and module Fq_target := Fq_target;
};

module Make = (Backend: Backend_intf) => {
  open Backend;

  module Verification_key = {
    [@deriving (bin_io, sexp)]
    type t = {
      alpha_beta: Fq_target.t,
      delta: G2.t,
      query: array(G1.t),
    };

    let map_to_two = (t, ~f) => {
      let (xs, ys) =
        List.fold_left(
          t,
          ~init=([], []),
          ~f=((xs, ys), a) => {
            let (x, y) = f(a);
            ([x, ...xs], [y, ...ys]);
          },
        );

      (List.rev(xs), List.rev(ys));
    };

    let fold_bits = ({alpha_beta, delta, query}) => {
      let g1s = Array.to_list(query);
      let g2s = [delta];
      let gts = [Fq_target.unitary_inverse(alpha_beta)];
      let (g1_elts, g1_signs) = map_to_two(g1s, ~f=G1.to_affine_exn);
      let non_zero_base_coordinate = a => {
        let x = Fqe.project_to_base(a);
        assert(!Fq.equal(x, Fq.zero));
        x;
      };

      let (g2_elts, g2_signs) =
        map_to_two(
          g2s,
          ~f=g => {
            let (x, y) = G2.to_affine_exn(g);
            (Fqe.to_list(x), non_zero_base_coordinate(y));
          },
        );

      let (gt_elts, gt_signs) =
        map_to_two(
          gts,
          ~f=g => {
            /* g is unitary, so (a, b) satisfy a quadratic over Fqe and thus
               b is determined by a up to sign */
            let (a, b) = g;
            (Fqe.to_list(a), non_zero_base_coordinate(b));
          },
        );

      open Fold;
      let of_fq_list_list = ls => {
        open Let_syntax;
        let%bind l = of_list(ls);
        let%bind x = of_list(l);
        Fq.fold_bits(x);
      };

      let parity_bit = x => N.test_bit(Fq.to_bigint(x), 0);
      let parity_bits = Fn.compose(map(~f=parity_bit), of_list);
      concat_map(of_list(g1_elts), ~f=Fq.fold_bits)
      +> of_fq_list_list(g2_elts)
      +> of_fq_list_list(gt_elts)
      +> parity_bits(g1_signs)
      +> parity_bits(g2_signs)
      +> parity_bits(gt_signs);
    };

    let fold = t => Fold.group3(~default=false, fold_bits(t));

    module Processed = {
      [@deriving (bin_io, sexp)]
      type t = {
        alpha_beta: Fq_target.t,
        delta_pc: Pairing.G2_precomputation.t,
        query: array(G1.t),
      };

      let create = ({alpha_beta, delta, query}) => {
        alpha_beta,
        delta_pc: Pairing.G2_precomputation.create(delta),
        query,
      };
    };
  };

  let check = (b, lab) =>
    if (b) {
      Ok();
    } else {
      Or_error.error_string(lab);
    };

  module Proof = {
    [@deriving (bin_io, sexp)]
    type t = {
      a: G1.t,
      b: G2.t,
      c: G1.t,
      delta_prime: G2.t,
      z: G1.t,
    };

    let is_well_formed = ({a, b, c, delta_prime, z}) => {
      open Or_error.Let_syntax;
      let err = x =>
        sprintf("proof was not well-formed (%s was off its curve)", x);

      let%bind () = check(G1.is_well_formed(a), err("a"));
      let%bind () = check(G2.is_well_formed(b), err("b"));
      let%bind () = check(G1.is_well_formed(c), err("c"));
      let%bind () =
        check(G2.is_well_formed(delta_prime), err("delta_prime"));

      let%map () = check(G1.is_well_formed(z), err("z"));
      ();
    };
  };

  let one_pc = lazy(Pairing.G2_precomputation.create(G2.one));

  let verify =
      (
        ~message=?,
        vk: Verification_key.Processed.t,
        input,
        {Proof.a, b, c, delta_prime, z} as proof,
      ) => {
    open Or_error.Let_syntax;
    let%bind () =
      check(
        Int.equal(List.length(input), Array.length(vk.query) - 1),
        "Input length was not as expected",
      );

    let%bind () = Proof.is_well_formed(proof);
    let input_acc =
      List.foldi(
        input,
        ~init=vk.query[0],
        ~f=(i, acc, x) => {
          let q = vk.query[1 + i];
          G1.(acc + x * q);
        },
      );

    let delta_prime_pc = Pairing.G2_precomputation.create(delta_prime);
    let test1 = {
      let l = Pairing.unreduced_pairing(a, b);
      let r1 = vk.alpha_beta;
      let r2 =
        Pairing.miller_loop(
          Pairing.G1_precomputation.create(input_acc),
          Lazy.force(one_pc),
        );

      let r3 =
        Pairing.miller_loop(
          Pairing.G1_precomputation.create(c),
          delta_prime_pc,
        );

      let test =
        Fq_target.(
          Pairing.final_exponentiation(unitary_inverse(l) * r2 * r3) * r1
        );

      Fq_target.(equal(test, one));
    };

    let%bind () = check(test1, "First pairing check failed");
    let test2 = {
      let ys = hash(~message?, ~a, ~b, ~c, ~delta_prime);
      let l =
        Pairing.miller_loop(
          Pairing.G1_precomputation.create(ys),
          delta_prime_pc,
        );

      let r =
        Pairing.miller_loop(
          Pairing.G1_precomputation.create(z),
          vk.delta_pc,
        );

      let test2 =
        Pairing.final_exponentiation(Fq_target.(l * unitary_inverse(r)));

      Fq_target.(equal(test2, one));
    };

    check(test2, "Second pairing check failed");
  };
};
