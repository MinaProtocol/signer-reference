open Core_kernel;

type fold('a, 's) = (~init: 's, ~f: ('s, 'a) => 's) => 's;

type t('a) = {fold: 's. fold('a, 's)};

let map = (t: t('a), ~f: 'a => 'b): t('b) => {
  fold: (~init, ~f as update) =>
    t.fold(~init, ~f=(acc, x) => update(acc, f(x))),
};

let concat = (t: t(t('a))): t('a) => {
  fold: (~init, ~f) =>
    t.fold(~init, ~f=(acc, inner) => inner.fold(~init=acc, ~f)),
};

let concat_map = (t: t('a), ~f: 'a => t('b)): t('b) => {
  fold: (~init, ~f as update) =>
    t.fold(~init, ~f=(acc, x) => f(x).fold(~init=acc, ~f=update)),
};

let init = (n, ~f as ith_elt) => {
  fold: (~init, ~f) => {
    let rec go = (i, acc) =>
      if (i == n) {
        acc;
      } else {
        go(i + 1, f(acc, ith_elt(i)));
      };

    go(0, init);
  },
};

include Monad.Make({
  type nonrec t('a) = t('a);

  let map = `Custom(map);

  let return = x => {fold: (~init, ~f) => f(init, x)};

  let bind = concat_map;
});

let to_list = (t: t('a)): list('a) =>
  List.rev(t.fold(~init=[], ~f=Fn.flip(List.cons)));

let of_list = (xs: list('a)): t('a) => {
  fold: (~init, ~f) => List.fold(xs, ~init, ~f),
};

let of_array = (xs: array('a)): t('a) => {
  fold: (~init, ~f) => Array.fold(xs, ~init, ~f),
};

let%test_unit "fold-to-list" =
  Quickcheck.test(Quickcheck.Generator.list(Int.quickcheck_generator), ~f=xs =>
    assert(xs == to_list(of_list(xs)))
  );

let sexp_of_t = (f, t) => List.sexp_of_t(f, to_list(t));

let compose = (t1: t('a), t2: t('a)): t('a) => {
  fold: (~init, ~f) => t2.fold(~init=t1.fold(~init, ~f), ~f),
};

let (+>) = compose;

let group3 = (~default, t: t('a)): t(('a, 'a, 'a)) => {
  fold: (~init, ~f) => {
    let (pt, bs) =
      t.fold(~init=(init, []), ~f=((pt, bs), b) =>
        switch (bs) {
        | [b2, b1, b0] =>
          let pt' = f(pt, (b0, b1, b2));
          (pt', [b]);
        | _ => (pt, [b, ...bs])
        }
      );

    switch (bs) {
    | [b2, b1, b0] => f(pt, (b0, b1, b2))
    | [b1, b0] => f(pt, (b0, b1, default))
    | [b0] => f(pt, (b0, default, default))
    | [] => pt
    | [_x1, _x2, _x3, _x4, ..._] => assert(false)
    };
  },
};

let%test_unit "group3" =
  Quickcheck.test(
    Quickcheck.Generator.list(Int.quickcheck_generator),
    ~f=xs => {
      let default = 0;
      let n = List.length(xs);
      let tuples = to_list(group3(~default, of_list(xs)));
      let k = List.length(tuples);
      let r = n mod 3;
      {
        let padded =
          xs
          @ (
            if (r == 0) {
              [];
            } else {
              List.init(3 - r, ~f=_ => default);
            }
          );

        let concated =
          List.concat_map(~f=((b1, b2, b3)) => [b1, b2, b3], tuples);

        [%test_eq: list(int)](padded, concated);
      };
      assert((n + 2) / 3 == k);
    },
  );

let string_bits = s => {
  let ith_bit_int = (n, i) => n lsr i land 1 == 1;
  {
    fold: (~init, ~f) =>
      String.fold(
        s,
        ~init,
        ~f=(acc, c) => {
          let c = Char.to_int(c);
          let update = (i, acc) => f(acc, ith_bit_int(c, i));
          update(0, acc)
          |> update(1)
          |> update(2)
          |> update(3)
          |> update(4)
          |> update(5)
          |> update(6)
          |> update(7);
        },
      ),
  };
};

let bool_t_to_string = {
  module State = {
    type t = {
      curr: int,
      acc: list(char),
      i: int,
    };
  };
  State.(
    t => {
      let {curr, i, acc} =
        t.fold(
          ~init={curr: 0, acc: [], i: 0},
          ~f=({curr, acc, i}, b) => {
            let curr =
              if (b) {
                curr lor 1 lsl i;
              } else {
                curr;
              };
            if (i == 7) {
              {i: 0, acc: [Char.of_int_exn(curr), ...acc], curr: 0};
            } else {
              {i: i + 1, acc, curr};
            };
          },
        );

      let cs =
        if (i == 0) {
          acc;
        } else {
          [Char.of_int_exn(curr), ...acc];
        };
      String.of_char_list(cs);
    }
  );
};

let string_triples = s => group3(~default=false, string_bits(s));
