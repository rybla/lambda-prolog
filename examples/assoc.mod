% title: Association lists
% tags: library, lists
% summary: Lookup, extension, update, deletion, and a small phone-book
%   example over lists of pairs.

module assoc.

accumulate lists.

type addassoc   A -> B -> list (pair A B) -> list (pair A B) -> o.
type lookup     A -> list (pair A B) -> B -> o.
type lookup1    A -> list (pair A B) -> B -> o.
type update     A -> B -> list (pair A B) -> list (pair A B) -> o.
type delassoc   A -> list (pair A B) -> list (pair A B) -> o.
type has_key    A -> list (pair A B) -> o.
type keys       list (pair A B) -> list A -> o.
type values     list (pair A B) -> list B -> o.
type from_zip   list A -> list B -> list (pair A B) -> o.
type phone      string -> int -> o.
type dial       string -> int -> o.

addassoc X Y L (pr X Y :: L).

lookup X L Y :- assoc X Y L.

% First binding only.
lookup1 X (pr X Y :: _) Y :- !.
lookup1 X (_ :: L) Y :- lookup1 X L Y.

delassoc X (pr X _ :: L) L.
delassoc X (P :: L) (P :: K) :- delassoc X L K.

update X Y L K :- delassoc X L M, !, addassoc X Y M K.
update X Y L K :- addassoc X Y L K.

has_key X L :- assoc X _ L.

keys L K :- domain L K.
values L V :- range L V.

from_zip Names Numbers Book :- zip Names Numbers Book.

phone "ada" 101.
phone "alonzo" 202.
phone "gottlob" 303.

dial Name Number :- phone Name Number.

% ---------------------------------------------------------------------------
% Example queries
query succeeds ? addassoc 1 2 nil L.
query succeeds ? lookup 1 (pr 1 2 :: pr 3 4 :: nil) Y.
query succeeds sample(1) ? lookup1 "a" (pr "a" 1 :: pr "a" 2 :: nil) Y.
query succeeds ? update 1 9 (pr 1 2 :: nil) L.
query succeeds ? delassoc 1 (pr 1 2 :: pr 3 4 :: nil) L.
query succeeds ? has_key 3 (pr 1 2 :: pr 3 4 :: nil).
query succeeds ? from_zip (1 :: 2 :: nil) (10 :: 20 :: nil) B.
query succeeds ? dial "ada" N.
query succeeds ? keys (pr 1 2 :: pr 3 4 :: nil) K.
