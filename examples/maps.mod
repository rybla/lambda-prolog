% title: Higher-order maps and folds
% tags: library, higher-order
% summary: mapfun, mappred, foldr, foldl, filter, partition, take_while,
%   qsort, and related combinators, plus a small census example.

module maps.

accumulate lists.

type mapfun       (A -> B) -> list A -> list B -> o.
type mappred      (A -> B -> o) -> list A -> list B -> o.
type map2         (A -> B -> C -> o) -> list A -> list B -> list C -> o.
type map_i        (int -> A -> B) -> list A -> list B -> o.
type map_i_from   int -> (int -> A -> B) -> list A -> list B -> o.
type foldr        (A -> B -> B) -> B -> list A -> B -> o.
type foldl        (A -> B -> A) -> A -> list B -> A -> o.
type foldr_pred   (A -> B -> B -> o) -> B -> list A -> B -> o.
type foldl_pred   (B -> A -> B -> o) -> B -> list A -> B -> o.
type scanl        (A -> B -> A) -> A -> list B -> list A -> o.
type filter       (A -> o) -> list A -> list A -> o.
type partition    (A -> o) -> list A -> list A -> list A -> o.
type take_while   (A -> o) -> list A -> list A -> o.
type drop_while   (A -> o) -> list A -> list A -> o.
type span         (A -> o) -> list A -> list A -> list A -> o.
type for_each     (A -> o) -> list A -> o.
type all_pred     (A -> o) -> list A -> o.
type exists_pred  (A -> o) -> list A -> o.
type find         (A -> o) -> list A -> A -> o.
type qsort        list int -> list int -> o.
type age          string -> int -> o.
type senior       string -> o.
type add          int -> int -> int -> o.

mapfun F nil nil.
mapfun F (X :: L) ((F X) :: K) :- mapfun F L K.

mappred P nil nil.
mappred P (X :: L) (Y :: K) :- P X Y, mappred P L K.

map2 P nil nil nil.
map2 P (X :: L) (Y :: K) (Z :: M) :- P X Y Z, map2 P L K M.

map_i F L K :- map_i_from 0 F L K.

map_i_from _ _ nil nil.
map_i_from N F (X :: L) ((F N X) :: K) :- M is N + 1, map_i_from M F L K.

% foldr F Init (X1 :: ... :: Xn :: nil)  (F X1 (F X2 (... (F Xn Init)))).
foldr F I nil I.
foldr F I (X :: L) (F X Y) :- foldr F I L Y.

% foldl F Init (X1 :: ... :: Xn :: nil)  (F (... (F Init X1) ...) Xn).
foldl F I nil I.
foldl F I (X :: L) Z :- foldl F (F I X) L Z.

foldr_pred P I nil I.
foldr_pred P I (X :: L) Z :- foldr_pred P I L Y, P X Y Z.

foldl_pred P I nil I.
foldl_pred P I (X :: L) Z :- P I X J, foldl_pred P J L Z.

scanl F I nil (I :: nil).
scanl F I (X :: L) (I :: K) :- scanl F (F I X) L K.

filter P nil nil.
filter P (X :: L) (X :: K) :- P X, !, filter P L K.
filter P (_ :: L) K :- filter P L K.

partition P nil nil nil.
partition P (X :: L) (X :: Ys) Ns :- P X, !, partition P L Ys Ns.
partition P (X :: L) Ys (X :: Ns) :- partition P L Ys Ns.

take_while _ nil nil.
take_while P (X :: L) (X :: K) :- P X, take_while P L K.
take_while P (X :: _) nil :- not (P X).

drop_while P (X :: L) K :- P X, !, drop_while P L K.
drop_while _ L L.

span P L A B :- take_while P L A, drop_while P L B.

for_each P nil.
for_each P (X :: L) :- P X, for_each P L.

all_pred P L :- for_each P L.

exists_pred P (X :: _) :- P X.
exists_pred P (_ :: L) :- exists_pred P L.

find P (X :: _) X :- P X.
find P (_ :: L) X :- find P L X.

qsort nil nil.
qsort (X :: L) K :-
  partition (y\ y =< X) L Le Gt,
  qsort Le A, qsort Gt B,
  append A (X :: B) K.

add X Y Z :- Z is X + Y.

age "bob" 30.
age "sue" 24.
age "ann" 30.
age "pat" 41.

senior N :- age N A, A > 25.

query succeeds ? mappred age ("bob" :: "sue" :: nil) L.
query succeeds ? mapfun (x\ x) (1 :: 2 :: nil) L.
query succeeds ? filter (x\ x > 1) (1 :: 2 :: 3 :: nil) L.
query succeeds ? partition (x\ x > 1) (1 :: 2 :: 3 :: nil) A B.
query succeeds ? qsort (3 :: 1 :: 2 :: nil) K.
query succeeds ? foldr_pred add 0 (1 :: 2 :: 3 :: nil) N.
query succeeds ? take_while (x\ x < 3) (1 :: 2 :: 3 :: nil) L.
query succeeds sample(3) ? senior N.
query succeeds ? map2 (x\ y\ z\ z is x + y) (1 :: 2 :: nil) (10 :: 20 :: nil) L.
