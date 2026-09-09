% title: Untyped λ-calculus
% tags: library, hoas, beta
% summary: HOAS encoding of the untyped λ-calculus: evaluation by meta-level
%   β-reduction, a copy/subst relation, one-step β, and a size measure.

module hoas_lambda.

kind tm  type.

type app    tm -> tm -> tm.
type abs    (tm -> tm) -> tm.
type eval   tm -> tm -> o.
type copy   tm -> tm -> o.
type subst  (tm -> tm) -> tm -> tm -> o.
type beta   tm -> tm -> o.
type size   tm -> int -> o.

eval (app M N) V :- eval M (abs R), eval N U, eval (R U) V.
eval (abs R) (abs R).

% copy is the identity on well-formed terms; it also realises substitution
% when the first argument is an applied abstraction (R U).
copy (app M N) (app P Q) :- copy M P, copy N Q.
copy (abs R) (abs S) :- pi x\ copy x x => copy (R x) (S x).

subst R N M :- copy (R N) M.

beta (app (abs R) N) M :- subst R N M.

size (app M N) K :- size M I, size N J, K is I + J + 1.
size (abs R) K :- pi x\ size x 1 => size (R x) N, K is N + 1.
