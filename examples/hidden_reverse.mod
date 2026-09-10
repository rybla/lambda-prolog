% title: Hidden accumulator
% tags: sigma, implication, hierarchy
% summary: reverse with an auxiliary rv that is existentially quantified and
%   implied, so it never appears in the module signature.

module hidden_reverse.

type reverse  list A -> list A -> o.
local rv.
type rv       list A -> list A -> list A -> o.

% rv is local to the module. Its clauses are not in the program until
% implication installs them for the duration of the call — a nested
% program that does not pollute the caller.
reverse L K :-
  (rv nil A A,
   (rv (X :: L1) A R :- rv L1 (X :: A) R))
  => rv L nil K.

% ---------------------------------------------------------------------------
% Examples
%   ?- reverse (1 :: 2 :: 3 :: nil) K.     % K = [3, 2, 1]
% The auxiliary rv is not in the exported program: a query `rv …` from
% outside this implication would not see those clauses.
