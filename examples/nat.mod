% title: Integers
% tags: library, arithmetic
% summary: Integer helpers on the pervasive @int@ type: comparisons, gcd,
%   exponentiation, factorial, Fibonacci, and a tiny expression evaluator.

module nat.

type min, max     int -> int -> int -> o.
type abs          int -> int -> o.
type between      int -> int -> int -> o.
type even, odd    int -> o.
type succ, pred   int -> int -> o.
type gcd          int -> int -> int -> o.
type lcm          int -> int -> int -> o.
type pow          int -> int -> int -> o.
type sign         int -> int -> o.
type divides      int -> int -> o.
type coprime      int -> int -> o.
type factorial    int -> int -> o.
type fib          int -> int -> o.
type clamp        int -> int -> int -> int -> o.
type square       int -> int -> o.

kind exp  type.
type elit    int -> exp.
type eplus   exp -> exp -> exp.
type etimes  exp -> exp -> exp.
type eminus  exp -> exp -> exp.
type eeval   exp -> int -> o.

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

lcm X Y Z :- gcd X Y D, D > 0, P is X * Y, Z is P div D.

pow _ 0 1.
pow X N Y :- N > 0, M is N - 1, pow X M Z, Y is X * Z.

sign X 1 :- X > 0.
sign 0 0.
sign X Y :- X < 0, Y is ~ 1.

divides D N :- D > 0, 0 is N mod D.

coprime X Y :- gcd X Y 1.

factorial 0 1.
factorial N K :- N > 0, M is N - 1, factorial M J, K is N * J.

fib 0 0.
fib 1 1.
fib N K :- N > 1, A is N - 1, B is N - 2, fib A I, fib B J, K is I + J.

clamp Lo Hi X Lo :- X < Lo.
clamp Lo Hi X Hi :- X > Hi.
clamp Lo Hi X X :- Lo =< X, X =< Hi.

square X Y :- Y is X * X.

eeval (elit N) N.
eeval (eplus A B) N :- eeval A I, eeval B J, N is I + J.
eeval (etimes A B) N :- eeval A I, eeval B J, N is I * J.
eeval (eminus A B) N :- eeval A I, eeval B J, N is I - J.

% ---------------------------------------------------------------------------
% Examples
%   ?- min 3 1 M.              % M = 1
%   ?- gcd 12 8 D.             % D = 4
%   ?- lcm 4 6 Z.              % Z = 12
%   ?- factorial 5 K.          % K = 120
%   ?- fib 7 N.                % N = 13
%   ?- between 1 3 N.          % N = 1, 2, 3
%   ?- pow 2 8 N.              % N = 256
%   ?- divides 3 12.
%   ?- eeval (eplus (elit 2) (etimes (elit 3) (elit 4))) N.   % N = 14
%   ?- clamp 0 10 (~ 3) C.     % C = 0
