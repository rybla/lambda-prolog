% title: Association lists
% tags: library, lists
% summary: Lookup, extension, update, and deletion for lists of pairs.

module assoc.

accumulate lists.

type addassoc   A -> B -> list (pair A B) -> list (pair A B) -> o.
type lookup     A -> list (pair A B) -> B -> o.
type update     A -> B -> list (pair A B) -> list (pair A B) -> o.
type delassoc   A -> list (pair A B) -> list (pair A B) -> o.

addassoc X Y L (pr X Y :: L).

lookup X L Y :- assoc X Y L.

delassoc X (pr X _ :: L) L.
delassoc X (P :: L) (P :: K) :- delassoc X L K.

update X Y L K :- delassoc X L M, !, addassoc X Y M K.
update X Y L K :- addassoc X Y L K.
