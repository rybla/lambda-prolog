% title: Combinatory Logic & Bracket Abstraction
% tags: combinators, bracket-abstraction, ski, compilation, hoas
% summary: SKI combinatory logic, bracket abstraction compiling HOAS lambda
%   abstractions into SKI combinator graphs using higher-order patterns,
%   and combinator graph reduction.

module combinators.

kind cterm type.

% Combinators and application
type c_s   cterm.
type c_k   cterm.
type c_i   cterm.
type c_app cterm -> cterm -> cterm.

% Bracket abstraction: converts a HOAS function (cterm -> cterm) into a closed SKI combinator
type bracket (cterm -> cterm) -> cterm -> o.
type reduce  cterm -> cterm -> o.
type step    cterm -> cterm -> o.

% Bracket abstraction using higher-order pattern matching:
% 1. [x] x = I
bracket (x\ x) c_i.

% 2. [x] C = K C  (C does not depend on x: higher-order pattern)
bracket (x\ C) (c_app c_k C).

% 3. [x] (F x) (G x) = S ([x] F x) ([x] G x)
bracket (x\ c_app (F x) (G x)) (c_app (c_app c_s SF) SG) :-
  bracket F SF,
  bracket G SG.

% Combinator reduction rules:
% I X ⟶ X
step (c_app c_i X) X.

% K X Y ⟶ X
step (c_app (c_app c_k X) _) X.

% S X Y Z ⟶ (X Z) (Y Z)
step (c_app (c_app (c_app c_s X) Y) Z) (c_app (c_app X Z) (c_app Y Z)).

% Contextual reduction
step (c_app M N) (c_app M1 N) :-
  step M M1.

step (c_app M N) (c_app M N1) :-
  step N N1.

% Transitive closure of reduction
reduce M M :-
  not (step M _), !.

reduce M V :-
  step M M1,
  reduce M1 V.

% ---------------------------------------------------------------------------
% Example queries
query succeeds ? bracket (x\ x) C.
query succeeds ? bracket (x\ c_i) C.
query succeeds ? bracket (x\ c_app (c_app c_s c_k) c_k) C.
query succeeds ? reduce (c_app c_i (c_app (c_app c_k c_s) c_i)) Res.
