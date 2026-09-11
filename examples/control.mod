% title: Control Combinators & Meta-Level Search Control
% tags: library, cut, extra-logical, higher-order, control
% summary: Fundamental control combinators (once, ifte, call, unless, ignore,
%   repeat_n, and_then, or_else) built from Prolog cut (!), failure, and
%   first-class goal variables of type o. Demonstrates how higher-order logic
%   programming seamlessly manipulates goals as first-class citizens.

module control.

% ============================================================================
% Predicate Signatures (Higher-Order Goals of Type o)
% ============================================================================

% In λProlog, the type 'o' represents propositions (goals and formulas).
% Predicates accepting arguments of type 'o' are higher-order control combinators.
type once      o -> o.
type ifte      o -> o -> o -> o.
type ignore    o -> o.
type call      o -> o.
type unless    o -> o -> o.
type repeat_n  int -> o -> o.
type and_then  o -> o -> o.
type or_else   o -> o -> o.

% ============================================================================
% Implementation
% ============================================================================

% Meta-call: executes goal G directly as a computation.
call G :- G.

% Explicit conjunction combinator (sequencing):
and_then A B :- A, B.

% Explicit disjunction combinator (choice):
or_else A B :- A ; B.

% once G: commits to the first successful solution of G, pruning alternative
% choice points upon backtracking.
once G :- G, !.

% if-then-else (ifte C T E):
% If condition C succeeds at least once, cut commits to the Then-branch T;
% if C fails to find any solutions, execution falls through to the Else-branch E.
ifte C T _ :- C, !, T.
ifte _ _ E :- E.

% unless C G:
% Negation-like control combinator: runs goal G only when condition C fails.
% If C succeeds, cut prunes and fail terminates that path.
unless C _ :- C, !, fail.
unless _ G :- G.

% ignore G:
% Runs G for side effects or partial binding, but always succeeds even if G fails.
ignore G :- G, !.
ignore _.

% repeat_n N G:
% Repeatedly executes goal G exactly N times in sequence.
repeat_n 0 _.
repeat_n N G :-
  N > 0,
  G,
  M is N - 1,
  repeat_n M G.

% ============================================================================
% Example Queries
% ============================================================================

query succeeds ? once true.
query succeeds ? once (true, true).
query fails ? once (fail, true).
query succeeds ? ifte true true fail.
query succeeds ? ifte fail fail true.
query succeeds ? ignore fail.
query succeeds ? unless fail true.
query fails ? unless true fail.
query succeeds ? call (true ; fail).
query succeeds ? repeat_n 3 true.
