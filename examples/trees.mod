% title: Binary trees
% tags: library, trees
% summary: Binary trees and binary search trees: membership, size, height,
%   traversals, mirror, map, and ordered insert/lookup.

module trees.

accumulate lists.

kind tree  type -> type.

type empty      tree A.
type node       A -> tree A -> tree A -> tree A.
type leaf       A -> tree A.
type tmember    A -> tree A -> o.
type tsize      tree A -> int -> o.
type theight    tree A -> int -> o.
type tempty     tree A -> o.
type tflatten   tree A -> list A -> o.
type preorder   tree A -> list A -> o.
type inorder    tree A -> list A -> o.
type postorder  tree A -> list A -> o.
type tmap       (A -> B) -> tree A -> tree B -> o.
type tmappred   (A -> B -> o) -> tree A -> tree B -> o.
type mirror     tree A -> tree A -> o.
type bst_insert int -> tree int -> tree int -> o.
type bst_lookup int -> tree int -> o.
type from_list  list int -> tree int -> o.
type demo_tree  tree int -> o.
type max2       int -> int -> int -> o.

leaf X (node X empty empty).

tempty empty.

tmember X (node X _ _).
tmember X (node _ L _) :- tmember X L.
tmember X (node _ _ R) :- tmember X R.

tsize empty 0.
tsize (node _ L R) N :- tsize L I, tsize R J, N is I + J + 1.

theight empty 0.
theight (node _ L R) N :-
  theight L I, theight R J, max2 I J M, N is M + 1.

max2 X Y X :- X >= Y.
max2 X Y Y :- X < Y.

% Inorder flatten.
tflatten T L :- inorder T L.

preorder empty nil.
preorder (node X L R) K :-
  preorder L A, preorder R B, append (X :: A) B K.

inorder empty nil.
inorder (node X L R) K :-
  inorder L A, inorder R B, append A (X :: B) K.

postorder empty nil.
postorder (node X L R) K :-
  postorder L A, postorder R B, append A B M, snoc X M K.

tmap F empty empty.
tmap F (node X L R) (node (F X) L' R') :- tmap F L L', tmap F R R'.

tmappred P empty empty.
tmappred P (node X L R) (node Y L' R') :-
  P X Y, tmappred P L L', tmappred P R R'.

mirror empty empty.
mirror (node X L R) (node X R' L') :- mirror L L', mirror R R'.

bst_insert X empty (node X empty empty).
bst_insert X (node Y L R) (node Y L' R) :- X =< Y, bst_insert X L L'.
bst_insert X (node Y L R) (node Y L R') :- X > Y, bst_insert X R R'.

bst_lookup X (node X _ _).
bst_lookup X (node Y L _) :- X < Y, bst_lookup X L.
bst_lookup X (node Y _ R) :- X > Y, bst_lookup X R.

from_list nil empty.
from_list (X :: L) T :- from_list L T0, bst_insert X T0 T.

demo_tree T :- from_list (5 :: 3 :: 8 :: 1 :: 4 :: nil) T.

% ---------------------------------------------------------------------------
% Examples
%   ?- tmember 2 (node 1 empty (node 2 empty empty)).
%   ?- tsize (node 1 empty empty) N.
%   ?- theight (node 1 (node 0 empty empty) empty) N.
%   ?- inorder (node 2 (node 1 empty empty) (node 3 empty empty)) L.
%   ?- mirror (node 1 (node 0 empty empty) empty) T.
%   ?- bst_insert 3 empty T, bst_insert 1 T U, bst_lookup 1 U.
%   ?- demo_tree T, inorder T L.                 % L sorted
%   ?- tmap (x\ x) (node 1 empty empty) T.
