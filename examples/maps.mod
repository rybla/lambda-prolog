% title: Higher-order maps
% tags: higher-order, predicates
% summary: mappred and mapfun take a predicate or function as an argument.

module maps.

type mappred  (A -> B -> o) -> list A -> list B -> o.
type mapfun   (A -> B) -> list A -> list B -> o.
type age      string -> int -> o.

mappred P nil nil.
mappred P (X :: L) (Y :: K) :- P X Y, mappred P L K.

mapfun F nil nil.
mapfun F (X :: L) ((F X) :: K) :- mapfun F L K.

age "bob" 30.
age "sue" 24.
