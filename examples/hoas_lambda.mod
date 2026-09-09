% title: HOAS evaluator
% tags: hoas, beta, lambda
% summary: Untyped λ-calculus encoded with higher-order abstract syntax;
%   substitution is meta-level β-reduction.

module hoas_lambda.

kind tm  type.

type app   tm -> tm -> tm.
type abs   (tm -> tm) -> tm.
type eval  tm -> tm -> o.

eval (app M N) V :- eval M (abs R), eval N U, eval (R U) V.
eval (abs R) (abs R).
