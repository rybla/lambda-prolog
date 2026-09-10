% title: Hypothetical reasoning
% tags: implication, hierarchy
% summary: Graph reachability by hypothetically adding edges with =>.
%   A triangle lemma, a detour through a fresh node, and the fact that
%   installed clauses do not leak past the implication.

module hypothetical.

kind node  type.

type a, b, c, d, e  node.
type edge           node -> node -> o.
type path           node -> node -> o.
type connected      node -> node -> o.
type cycle3         o.
type via_e          o.

path X Y :- edge X Y.
path X Z :- edge X Y, path Y Z.

% A base graph: a → b → d. Adding edge b c hypothetically unlocks a → c.
edge a b.
edge b d.

connected X Y :- path X Y.

% A local lemma: if we assume a triangle on a,b,c then path a c.
cycle3 :-
  (edge a b, edge b c, edge c a) => (path a c, !).

% Temporarily add e with d → e → a, so b reaches a.
via_e :- (edge d e, edge e a) => (path b a, !).

% ---------------------------------------------------------------------------
% Examples
%   ?- path a d.                         % base graph
%   ?- path a c.                         % fails (no edge b c)
%   ?- edge b c => path a c.             % succeeds hypothetically
%   ?- connected a d.
%   ?- cycle3.
%   ?- via_e.                            % walk b → d → e → a
%   ?- (edge d a) => path b a.           % walk b → d → a
