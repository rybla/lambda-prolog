% title: Lists
% tags: horn, lists
% summary: Classic list programs — append, reverse, member — as first-order Horn clauses.

module lists.

type append   list A -> list A -> list A -> o.
type reverse  list A -> list A -> o.
type member   A -> list A -> o.

append nil L L.
append (X :: L) K (X :: M) :- append L K M.

reverse nil nil.
reverse (X :: L) K :- reverse L M, append M (X :: nil) K.

member X (X :: L).
member X (Y :: L) :- member X L.
