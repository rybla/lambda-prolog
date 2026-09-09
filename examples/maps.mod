% title: Higher-order maps and folds
% tags: library, higher-order
% summary: mapfun, mappred, foldr, foldl, filter, partition, and for_each —
%   the usual higher-order list combinators, plus a small example relation.

module maps.

accumulate lists.

type mapfun       (A -> B) -> list A -> list B -> o.
type mappred      (A -> B -> o) -> list A -> list B -> o.
type map2         (A -> B -> C -> o) -> list A -> list B -> list C -> o.
type foldr        (A -> B -> B) -> B -> list A -> B -> o.
type foldl        (A -> B -> A) -> A -> list B -> A -> o.
type filter       (A -> o) -> list A -> list A -> o.
type partition    (A -> o) -> list A -> list A -> list A -> o.
type for_each     (A -> o) -> list A -> o.
type all_pred     (A -> o) -> list A -> o.
type exists_pred  (A -> o) -> list A -> o.
type find         (A -> o) -> list A -> A -> o.
type age          string -> int -> o.

mapfun F nil nil.
mapfun F (X :: L) ((F X) :: K) :- mapfun F L K.

mappred P nil nil.
mappred P (X :: L) (Y :: K) :- P X Y, mappred P L K.

map2 P nil nil nil.
map2 P (X :: L) (Y :: K) (Z :: M) :- P X Y Z, map2 P L K M.

% foldr F Init (X1 :: ... :: Xn :: nil)  (F X1 (F X2 (... (F Xn Init)))).
foldr F I nil I.
foldr F I (X :: L) (F X Y) :- foldr F I L Y.

% foldl F Init (X1 :: ... :: Xn :: nil)  (F (... (F Init X1) ...) Xn).
foldl F I nil I.
foldl F I (X :: L) Z :- foldl F (F I X) L Z.

filter P nil nil.
filter P (X :: L) (X :: K) :- P X, !, filter P L K.
filter P (_ :: L) K :- filter P L K.

partition P nil nil nil.
partition P (X :: L) (X :: Ys) Ns :- P X, !, partition P L Ys Ns.
partition P (X :: L) Ys (X :: Ns) :- partition P L Ys Ns.

for_each P nil.
for_each P (X :: L) :- P X, for_each P L.

all_pred P L :- for_each P L.

exists_pred P (X :: _) :- P X.
exists_pred P (_ :: L) :- exists_pred P L.

find P (X :: _) X :- P X.
find P (_ :: L) X :- find P L X.

age "bob" 30.
age "sue" 24.
age "ann" 30.
