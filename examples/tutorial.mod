% title: Tutorial
% tags: intro, lists, pi, implication
% summary: A walk through λProlog syntax, lists, and the scoping primitives pi and =>.

module tutorial.

% First-order Horn clauses look like Prolog, but terms are simply typed
% and fully curried.

type append  list A -> list A -> list A -> o.

append nil L L.
append (X :: L) K (X :: M) :- append L K M.

% Implication (=>) adds a clause for the duration of a goal. This is
% hypothetical reasoning: "if we had edge a b, could we prove path a c?"

type edge    A -> A -> o.
type path    A -> A -> o.

path X Y :- edge X Y.
path X Z :- edge X Y, path Y Z.

% Universal goals (pi) introduce a fresh eigenvariable. Combined with
% implication this is the characteristic "hierarchical" structure of
% hereditary Harrop programs: a local signature and a local program.

type ident   A -> A -> o.
ident X X.

% Try:
%   ?- append (1 :: 2 :: nil) (3 :: nil) L.
%   ?- edge a b => edge b c => path a c.
%   ?- pi x\ ident x x.
