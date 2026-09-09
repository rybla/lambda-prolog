% title: Tactics and tacticals
% tags: higher-order, search
% summary: Tactics as relations on object-goals; tacticals (then, orelse,
%   repeat) are higher-order predicates that combine them.

module tacticals.

kind g  type.

type truegoal, p, q, r    g.
type andgoal              g -> g -> g.

type idtac     g -> g -> o.
type orelse    (g -> g -> o) -> (g -> g -> o) -> g -> g -> o.
type then      (g -> g -> o) -> (g -> g -> o) -> g -> g -> o.
type maptac    (g -> g -> o) -> g -> g -> o.
type ptac, qtac, rtac     g -> g -> o.

idtac G G.

orelse R1 R2 G1 G2 :- R1 G1 G2.
orelse R1 R2 G1 G2 :- R2 G1 G2.

maptac R truegoal truegoal.
maptac R (andgoal G1 G2) (andgoal G3 G4) :- maptac R G1 G3, maptac R G2 G4.
maptac R G1 G2 :- R G1 G2.

then R1 R2 G1 G2 :- R1 G1 G3, maptac R2 G3 G2.

ptac p (andgoal q r).
qtac q truegoal.
rtac r truegoal.
