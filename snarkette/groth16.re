open Core_kernel;

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
      query: array(G1.t),
      delta: G2.t,
      alpha_beta: Fq_target.t,
    };

    type vk = t;

    module Processed = {
      [@deriving (bin_io, sexp)]
      type t = {
        query: array(G1.t),
        alpha_beta: Fq_target.t,
        delta: Pairing.G2_precomputation.t,
      };

      let create = ({query, alpha_beta, delta}: vk) => {
        alpha_beta,
        delta: Pairing.G2_precomputation.create(delta),
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
    };

    let is_well_formed = ({a, b, c}) => {
      open Or_error.Let_syntax;
      let err = x =>
        sprintf("proof was not well-formed (%s was off its curve)", x);

      let%bind () = check(G1.is_well_formed(a), err("a"));
      let%bind () = check(G2.is_well_formed(b), err("b"));
      check(G1.is_well_formed(c), err("c"));
    };
  };

  let one_pc = lazy(Pairing.G2_precomputation.create(G2.one));

  let verify =
      (vk: Verification_key.Processed.t, input, {Proof.a, b, c} as proof) => {
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

    let test1 = {
      let l = Pairing.unreduced_pairing(a, b);
      let r1 = vk.alpha_beta;
      let r2 =
        Pairing.miller_loop(
          Pairing.G1_precomputation.create(input_acc),
          Lazy.force(one_pc),
        );

      let r3 =
        Pairing.miller_loop(Pairing.G1_precomputation.create(c), vk.delta);

      let test =
        Fq_target.(
          Pairing.final_exponentiation(unitary_inverse(l) * r2 * r3) * r1
        );

      Fq_target.(equal(test, one));
    };

    check(test1, "Pairing check failed");
  };
};
