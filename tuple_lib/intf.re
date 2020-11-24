open Core_kernel;

module type S = {
  [@deriving (bin_io, sexp, eq, compare)]
  type t('a);

  let iter: (t('a), ~f: 'a => unit) => unit;

  let map: (t('a), ~f: 'a => 'b) => t('b);

  let map2: (t('a), t('b), ~f: ('a, 'b) => 'c) => t('c);
};
