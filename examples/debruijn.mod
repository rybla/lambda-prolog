% title: HOAS and de Bruijn Conversion
% tags: hoas, debruijn, syntax, representation, hypothetical
% summary: Bidirectional conversion between Higher-Order Abstract Syntax (HOAS)
%   and first-order de Bruijn indexed terms using hypothetical reasoning,
%   along with shifting, substitution, and evaluation on de Bruijn terms.

module debruijn.

kind htm type.
kind dtm type.

% HOAS constructors
type happ htm -> htm -> htm.
type habs (htm -> htm) -> htm.

% de Bruijn constructors
type dvar int -> dtm.
type dapp dtm -> dtm -> dtm.
type dlam dtm -> dtm.

% Conversion predicates
type hoas_to_debruijn htm -> dtm -> o.
type h2d               int -> htm -> dtm -> o.
type pos               htm -> int -> o.

type debruijn_to_hoas dtm -> htm -> o.
type d2h              dtm -> list htm -> htm -> o.

% de Bruijn operations
type d_shift          int -> int -> dtm -> dtm -> o.
type d_subst          dtm -> int -> dtm -> dtm -> o.
type d_beta           dtm -> dtm -> o.
type d_eval           dtm -> dtm -> o.

% --- HOAS to de Bruijn ---
% We track binder depth. When traversing under a lambda with eigenvariable x,
% we hypothesize (pos x CurrDepth), and increment depth for the body.
hoas_to_debruijn H D :-
  h2d 0 H D.

h2d Curr (happ M N) (dapp DM DN) :-
  h2d Curr M DM,
  h2d Curr N DN.

h2d Curr (habs R) (dlam DBody) :-
  Next is Curr + 1,
  pi x\ (pos x Curr => h2d Next (R x) DBody).

h2d Curr X (dvar Idx) :-
  pos X BindDepth,
  Idx is Curr - BindDepth - 1.

% --- de Bruijn to HOAS ---
% We maintain an environment of HOAS variables corresponding to de Bruijn indices.
% Pushing a fresh eigenvariable onto the head corresponds to index 0.
debruijn_to_hoas D H :-
  d2h D nil H.

d2h (dvar 0) (X :: _) X.
d2h (dvar I) (_ :: Xs) X :-
  I > 0,
  I1 is I - 1,
  d2h (dvar I1) Xs X.

d2h (dapp M N) Env (happ HM HN) :-
  d2h M Env HM,
  d2h N Env HN.

d2h (dlam D) Env (habs R) :-
  pi x\ d2h D (x :: Env) (R x).

% --- de Bruijn Shifting and Substitution ---
% d_shift Cutoff Amount In Out
d_shift C _ (dvar I) (dvar I) :-
  I < C.
d_shift C K (dvar I) (dvar Res) :-
  I >= C,
  Res is I + K.
d_shift C K (dapp M N) (dapp M1 N1) :-
  d_shift C K M M1,
  d_shift C K N N1.
d_shift C K (dlam M) (dlam M1) :-
  C1 is C + 1,
  d_shift C1 K M M1.

% d_subst Val J In Out : substitute Val for free index J in In
d_subst Val J (dvar I) Val :-
  I = J.
d_subst _ J (dvar I) (dvar Res) :-
  I > J,
  Res is I - 1.
d_subst _ J (dvar I) (dvar I) :-
  I < J.
d_subst Val J (dapp M N) (dapp M1 N1) :-
  d_subst Val J M M1,
  d_subst Val J N N1.
d_subst Val J (dlam M) (dlam M1) :-
  d_shift 0 1 Val Val1,
  J1 is J + 1,
  d_subst Val1 J1 M M1.

% One-step beta reduction: (λ. M) N ⟶ M[0 := N]
d_beta (dapp (dlam M) N) Res :-
  d_subst N 0 M Res.

% Big-step evaluation on de Bruijn terms
d_eval (dlam M) (dlam M).
d_eval (dapp M N) V :-
  d_eval M (dlam Body),
  d_eval N VN,
  d_subst VN 0 Body Step,
  d_eval Step V.

% ---------------------------------------------------------------------------
% Example queries:
%   ?- hoas_to_debruijn (habs (x\ x)) D.
%      D = dlam (dvar 0)
%   ?- hoas_to_debruijn (habs (x\ habs (y\ x))) D.
%      D = dlam (dlam (dvar 1))
%   ?- debruijn_to_hoas (dlam (dvar 0)) H.
%   ?- d_eval (dapp (dlam (dvar 0)) (dlam (dlam (dvar 1)))) V.
