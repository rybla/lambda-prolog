% title: Tactics and tacticals
% tags: library, higher-order, search
% summary: Tactics as relations on object-goals; tacticals then, orelse,
%   try, repeat, first, progress, and complete compose them.

module tacticals.

kind g  type.

type truegoal             g.
type andgoal              g -> g -> g.
type orgoal               g -> g -> g.
type p, q, r, s           g.

type idtac     g -> g -> o.
type orelse    (g -> g -> o) -> (g -> g -> o) -> g -> g -> o.
type first     (g -> g -> o) -> (g -> g -> o) -> g -> g -> o.
type then      (g -> g -> o) -> (g -> g -> o) -> g -> g -> o.
type maptac    (g -> g -> o) -> g -> g -> o.
type try       (g -> g -> o) -> g -> g -> o.
type repeat    (g -> g -> o) -> g -> g -> o.
type progress  (g -> g -> o) -> g -> g -> o.
type complete  (g -> g -> o) -> g -> g -> o.
type ptac, qtac, rtac, stac     g -> g -> o.

idtac G G.

orelse R1 R2 G1 G2 :- R1 G1 G2.
orelse R1 R2 G1 G2 :- R2 G1 G2.

first R1 R2 G1 G2 :- orelse R1 R2 G1 G2.

try R G1 G2 :- orelse R idtac G1 G2.

maptac R truegoal truegoal.
maptac R (andgoal G1 G2) (andgoal G3 G4) :- maptac R G1 G3, maptac R G2 G4.
maptac R (orgoal G1 G2) (orgoal G3 G4) :- maptac R G1 G3, maptac R G2 G4.
maptac R G1 G2 :- R G1 G2.

then R1 R2 G1 G2 :- R1 G1 G3, maptac R2 G3 G2.

repeat R G1 G2 :- orelse (then R (repeat R)) idtac G1 G2.

progress R G1 G2 :- R G1 G2, not (G1 = G2).

complete R G1 truegoal :- R G1 G2, G2 = truegoal.

ptac p (andgoal q r).
qtac q truegoal.
rtac r truegoal.
stac s p.

query succeeds ? idtac p p.
query succeeds ? ptac p (andgoal q r).
query succeeds ? then ptac (orelse qtac rtac) p (andgoal truegoal truegoal).
query fails ? complete (then ptac (orelse qtac rtac)) p truegoal.
query succeeds ? try stac q q.                   % stac does not apply; idtac
query succeeds ? progress ptac p G.              % G ≠ p
query succeeds ? first qtac ptac p (andgoal q r).
