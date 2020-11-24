open Core_kernel;

[@deriving (bin_io, sexp, eq, compare)]
type t('a) = ('a, 'a, 'a, 'a);

let get = ((x0, x1, x2, x3): t('a), i: Four.t) =>
  switch (i) {
  | Zero => x0
  | One => x1
  | Two => x2
  | Three => x3
  };

let map = ((x1, x2, x3, x4), ~f) => (f(x1), f(x2), f(x3), f(x4));

let map2 = ((x1, x2, x3, x4), (y1, y2, y3, y4), ~f) => (
  f(x1, y1),
  f(x2, y2),
  f(x3, y3),
  f(x4, y4),
);

let iter = ((x1, x2, x3, x4), ~f) => {
  f(x1);
  f(x2);
  f(x3);
  f(x4);
};
