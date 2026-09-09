% title: Binary trees
% tags: library, trees, hoas
% summary: Binary trees with membership, size, flattening, and a functional
%   map. Flattening reuses append from lists.mod.

module trees.

accumulate lists.

kind tree  type -> type.

type empty     tree A.
type node      A -> tree A -> tree A -> tree A.
type tmember   A -> tree A -> o.
type tsize     tree A -> int -> o.
type tflatten  tree A -> list A -> o.
type tmap      (A -> B) -> tree A -> tree B -> o.

tmember X (node X _ _).
tmember X (node _ L _) :- tmember X L.
tmember X (node _ _ R) :- tmember X R.

tsize empty 0.
tsize (node _ L R) N :- tsize L I, tsize R J, N is I + J + 1.

tflatten empty nil.
tflatten (node X L R) K :-
  tflatten L A, tflatten R B, append A (X :: B) K.

tmap F empty empty.
tmap F (node X L R) (node (F X) L' R') :- tmap F L L', tmap F R R'.
