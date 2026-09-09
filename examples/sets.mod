% title: Finite sets
% tags: library, lists
% summary: Finite sets as lists, using membership from lists.mod.

module sets.

accumulate lists.

type subset       list A -> list A -> o.
type union        list A -> list A -> list A -> o.
type intersect    list A -> list A -> list A -> o.
type difference   list A -> list A -> list A -> o.
type disjoint     list A -> list A -> o.
type insert       A -> list A -> list A -> o.
type delete       A -> list A -> list A -> o.
type seteq        list A -> list A -> o.
type card         list A -> int -> o.

subset nil _.
subset (X :: S) T :- memb X T, subset S T.

union S T U :- join S T U.

intersect nil _ nil.
intersect (X :: S) T (X :: U) :- memb X T, !, intersect S T U.
intersect (_ :: S) T U :- intersect S T U.

difference nil _ nil.
difference (X :: S) T U :- memb X T, !, difference S T U.
difference (X :: S) T (X :: U) :- difference S T U.

disjoint nil _.
disjoint (X :: S) T :- not (memb X T), disjoint S T.

insert X S S :- memb X S, !.
insert X S (X :: S).

delete X S T :- select X S T, !.
delete _ S S.

seteq S T :- subset S T, subset T S.

card S N :- nub S K, length K N.
