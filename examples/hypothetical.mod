% title: Hypothetical reasoning
% tags: implication, hierarchy
% summary: Graph reachability by hypothetically adding edges with =>.
%   The installed clause is scoped: it does not leak past the implication.

module hypothetical.

kind node  type.

type a, b, c, d    node.
type edge          node -> node -> o.
type path          node -> node -> o.
type connected     node -> node -> o.

path X Y :- edge X Y.
path X Z :- edge X Y, path Y Z.

% A base graph: a → b → d. Adding edge b c hypothetically unlocks a → c.
edge a b.
edge b d.

% connected X Y holds if Y is reachable from X in the current graph.
connected X Y :- path X Y.
