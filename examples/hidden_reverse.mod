% title: Hidden Accumulator & Scoped Helper Predicates
% tags: sigma, implication, hierarchy, information-hiding, hypothetical
% summary: Demonstrates information hiding and local helper encapsulation using
%   hereditary Harrop implication (=>) and local declarations. Implements a
%   linear-time tail-recursive list reversal where the accumulator predicate
%   (rv) exists only during the execution of reverse and is completely hidden
%   from caller modules.

module hidden_reverse.

% ============================================================================
% Public Signature & Local Declarations
% ============================================================================

% Public entry point for list reversal:
type reverse  list A -> list A -> o.

% The 'local' directive hides predicate 'rv' from outside modules.
% In standard first-order Prolog, auxiliary helper predicates with accumulators
% pollute the global predicate table. In λProlog, 'local' ensures rv cannot
% be queried or backchained against outside this module.
local rv.
type rv       list A -> list A -> list A -> o.

% ============================================================================
% Implementation using Hypothetical Implication (=>)
% ============================================================================

% In traditional logic programming, auxiliary predicates require clauses to
% sit permanently in the database.
% In λProlog, the clauses defining 'rv' are NOT in the program statically.
% Instead, the implication connective (D => G) dynamically installs the clauses
% for the duration of proving the goal (rv L nil K).
%
% Semantics of (D => G):
%   1. The base case: rv nil Acc Acc.
%   2. The recursive step: rv (X :: L1) Acc R :- rv L1 (X :: Acc) R.
% These clauses are consed onto the active program state, the goal is executed,
% and upon completion or backtracking, the clauses are popped off the program.
% This creates a clean, ephemeral lexical scope for the helper definition.

reverse L K :-
  (rv nil A A,
   (rv (X :: L1) A R :- rv L1 (X :: A) R))
  => rv L nil K.

% ============================================================================
% Example Queries
% ============================================================================

% Reversing a 3-element list:
query succeeds ? reverse (1 :: 2 :: 3 :: nil) K.

% Reversing an empty list:
query succeeds ? reverse nil nil.

% Palindrome check using reverse:
query succeeds ? reverse (1 :: 2 :: 1 :: nil) (1 :: 2 :: 1 :: nil).
