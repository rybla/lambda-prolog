% title: Finite sets
% tags: library, lists
% summary: Finite sets as lists without regard to order: algebra, tests,
%   powerset (small), and conversion from lists.

module sets.

accumulate lists.

type subset       list A -> list A -> o.
type psubset      list A -> list A -> o.
type union        list A -> list A -> list A -> o.
type intersect    list A -> list A -> list A -> o.
type difference   list A -> list A -> list A -> o.
type symdiff      list A -> list A -> list A -> o.
type disjoint     list A -> list A -> o.
type insert       A -> list A -> list A -> o.
type delete       A -> list A -> list A -> o.
type seteq        list A -> list A -> o.
type card         list A -> int -> o.
type empty        list A -> o.
type singleton    A -> list A -> o.
type from_list    list A -> list A -> o.
type add_all      list A -> list A -> list A -> o.
type powerset     list A -> list A -> o.

empty nil.

singleton X (X :: nil).

subset nil _.
subset (X :: S) T :- memb X T, subset S T.

psubset S T :- subset S T, not (subset T S).

union S T U :- join S T U.

intersect nil _ nil.
intersect (X :: S) T (X :: U) :- memb X T, !, intersect S T U.
intersect (_ :: S) T U :- intersect S T U.

difference nil _ nil.
difference (X :: S) T U :- memb X T, !, difference S T U.
difference (X :: S) T (X :: U) :- difference S T U.

symdiff S T U :-
  difference S T A,
  difference T S B,
  append A B U.

disjoint nil _.
disjoint (X :: S) T :- not (memb X T), disjoint S T.

insert X S S :- memb X S, !.
insert X S (X :: S).

delete X S T :- select X S T, !.
delete _ S S.

seteq S T :- subset S T, subset T S.

card S N :- nub S K, length K N.

from_list L S :- nub L S.

add_all nil S S.
add_all (X :: L) S T :- insert X S S1, add_all L S1 T.

% powerset S P  — P is some subset of S (enumerates 2^|S| solutions).
powerset nil nil.
powerset (X :: S) (X :: P) :- powerset S P.
powerset (_ :: S) P :- powerset S P.

query succeeds ? subset (1 :: nil) (1 :: 2 :: nil).
query succeeds ? union (1 :: nil) (1 :: 2 :: nil) U.
query succeeds ? intersect (1 :: 2 :: nil) (2 :: 3 :: nil) I.
query succeeds ? difference (1 :: 2 :: 3 :: nil) (2 :: nil) D.
query succeeds ? disjoint (1 :: nil) (2 :: nil).
query succeeds ? seteq (1 :: 2 :: nil) (2 :: 1 :: nil).
query succeeds ? card (1 :: 1 :: 2 :: nil) N.
query succeeds sample(4) ? powerset (1 :: 2 :: nil) P.
query succeeds ? psubset (1 :: nil) (1 :: 2 :: nil).
query succeeds ? add_all (1 :: 1 :: 2 :: nil) nil S.
