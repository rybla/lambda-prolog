% title: Tutorial
% tags: intro, lists, pi, implication
% summary: A walk through λProlog: typed Horn clauses, lists, hypothetical
%   implication, universal goals, and a first HOAS snippet.

module tutorial.

% First-order Horn clauses look like Prolog, but terms are simply typed
% and fully curried. Capitalised identifiers are logic variables.

type append  list A -> list A -> list A -> o.
type member  A -> list A -> o.
type reverse list A -> list A -> o.

append nil L L.
append (X :: L) K (X :: M) :- append L K M.

member X (X :: _).
member X (_ :: L) :- member X L.

reverse nil nil.
reverse (X :: L) K :- reverse L M, append M (X :: nil) K.

% Implication (=>) adds a clause for the duration of a goal. This is
% hypothetical reasoning: "if we had edge a b, could we prove path a c?"

kind node  type.
type a, b, c     node.
type edge        node -> node -> o.
type path        node -> node -> o.

path X Y :- edge X Y.
path X Z :- edge X Y, path Y Z.

% Universal goals (pi) introduce a fresh eigenvariable. Combined with
% implication this is the hierarchical structure of hereditary Harrop
% programs: a local signature and a local program.

type ident   A -> A -> o.
ident X X.

% Higher-order abstract syntax: object binders are meta-level lambdas.
kind tm  type.
type abs   (tm -> tm) -> tm.
type app   tm -> tm -> tm.
type copy  tm -> tm -> o.
copy (app M N) (app P Q) :- copy M P, copy N Q.
copy (abs R) (abs S) :- pi x\ copy x x => copy (R x) (S x).

query succeeds ? append (1 :: 2 :: nil) (3 :: nil) L.
query succeeds sample(3) ? append L K (1 :: 2 :: nil).
query succeeds ? member 2 (1 :: 2 :: 3 :: nil).
query succeeds ? reverse (1 :: 2 :: 3 :: nil) K.
query succeeds ? edge a b => edge b c => path a c.
query succeeds ? pi x\ ident x x.
query succeeds ? copy (abs (x\ x)) M.
query fails ? copy (abs (x\ app x x)) M.
