% title: Untyped λ-calculus
% tags: library, hoas, beta
% summary: HOAS encoding of the untyped λ-calculus: evaluation, copy/subst,
%   one-step β, size, Church numerals, and the I/K/S combinators.

module hoas_lambda.

kind tm  type.

type app     tm -> tm -> tm.
type abs     (tm -> tm) -> tm.
type eval    tm -> tm -> o.
type copy    tm -> tm -> o.
type subst   (tm -> tm) -> tm -> tm -> o.
type beta    tm -> tm -> o.
type step_beta tm -> tm -> o.
type nf       tm -> tm -> o.
type alpha_equiv tm -> tm -> o.
type eq_hyp   tm -> tm -> o.
type size    tm -> int -> o.
type is_abs  tm -> o.
type is_app  tm -> o.
type ntimes  int -> tm -> tm -> tm -> o.
type ch      int -> (tm -> tm -> tm) -> o.
type church  int -> tm -> o.
type plus_ch tm -> tm -> tm -> o.
type combinator string -> tm -> o.

eval (app M N) V :- eval M (abs R), eval N U, eval (R U) V.
eval (abs R) (abs R).

% copy is the identity on well-formed terms; it also realises substitution
% when the first argument is an applied abstraction (R U).
copy (app M N) (app P Q) :- copy M P, copy N Q.
copy (abs R) (abs S) :- pi x\ copy x x => copy (R x) (S x).

subst R N M :- copy (R N) M.

beta (app (abs R) N) M :- subst R N M.

step_beta (app (abs R) N) M :- subst R N M.
step_beta (app M N) (app M1 N) :- step_beta M M1.
step_beta (app M N) (app M N1) :- step_beta N N1.

% Full normal form reduction (evaluates under lambda abstractions)
nf (abs R) (abs S) :-
  pi x\ nf (R x) (S x).
nf (app M N) Res :-
  nf M (abs R), !,
  nf N VN,
  subst R VN Body,
  nf Body Res.
nf (app M N) (app M1 N1) :-
  nf M M1,
  nf N N1.
nf X X.

% Alpha-equivalence check via hypothetical reasoning
alpha_equiv X Y :- eq_hyp X Y, !.
alpha_equiv (app M1 N1) (app M2 N2) :-
  alpha_equiv M1 M2,
  alpha_equiv N1 N2.
alpha_equiv (abs R1) (abs R2) :-
  pi x\ (eq_hyp x x => alpha_equiv (R1 x) (R2 x)).

size (app M N) K :- size M I, size N J, K is I + J + 1.
size (abs R) K :- pi x\ size x 1 => size (R x) N, K is N + 1.

is_abs (abs _).
is_app (app _ _).

% ntimes N F X T  — T is F applied N times to X.
ntimes 0 _ X X.
ntimes N F X (app F Y) :- N > 0, M is N - 1, ntimes M F X Y.

% Church numeral as a meta-level function R, then wrapped in abs.
ch 0 (f\ x\ x).
ch N (f\ x\ app f (R f x)) :- N > 0, M is N - 1, ch M R.

church N (abs (f\ abs (x\ R f x))) :- ch N R.

% plus M N = λf. λx. M f (N f x)
plus_ch M N (abs (f\ abs (x\ app (app M f) (app (app N f) x)))).

combinator "I" (abs (x\ x)).
combinator "K" (abs (x\ abs (y\ x))).
combinator "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).

% ---------------------------------------------------------------------------
% Example queries
query succeeds ? eval (abs (x\ x)) V.
query succeeds ? eval (app (abs (x\ x)) (abs (y\ y))) V.
query succeeds ? copy (abs (x\ x)) M.
query succeeds ? size (abs (x\ x)) N.
query succeeds ? subst (x\ x) (abs (y\ y)) M.
query succeeds ? beta (app (abs (x\ x)) (abs (y\ y))) M.
query succeeds ? church 2 C, eval (app (app C (abs (s\ s))) (abs (z\ z))) V.
query succeeds ? combinator "K" K, combinator "I" I, eval (app (app K I) (abs (w\ w))) V.
query succeeds ? is_abs (abs (x\ x)).
