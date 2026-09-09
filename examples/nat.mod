% title: Integers
% tags: library, arithmetic
% summary: Integer helpers on the pervasive @int@ type: min, max, abs,
%   between, even, odd, gcd, and exponentiation, using @is@ and comparison
%   goals.

module nat.

type min, max     int -> int -> int -> o.
type abs          int -> int -> o.
type between      int -> int -> int -> o.
type even, odd    int -> o.
type succ, pred   int -> int -> o.
type gcd          int -> int -> int -> o.
type pow          int -> int -> int -> o.
type sign         int -> int -> o.

min X Y X :- X =< Y.
min X Y Y :- Y < X.

max X Y Y :- X =< Y.
max X Y X :- Y < X.

abs X X :- X >= 0.
abs X Y :- X < 0, Y is ~ X.

% between Lo Hi N  enumerates N = Lo, Lo+1, ..., Hi.
between Lo Hi Lo :- Lo =< Hi.
between Lo Hi N :- Lo < Hi, M is Lo + 1, between M Hi N.

even N :- 0 is N mod 2.
odd N :- 1 is N mod 2.

succ X Y :- Y is X + 1.
pred X Y :- Y is X - 1.

gcd X 0 X :- X >= 0.
gcd X Y Z :- Y > 0, R is X mod Y, gcd Y R Z.

pow _ 0 1.
pow X N Y :- N > 0, M is N - 1, pow X M Z, Y is X * Z.

sign X 1 :- X > 0.
sign 0 0.
sign X Y :- X < 0, Y is ~ 1.
