% title: Simply-typed λ-calculus
% tags: library, hoas, pi, implication
% summary: STLC with HOAS: a base type, a constant, type inference, and
%   a well-formedness check. Application of an abstraction is meta-level
%   substitution.

module typeinf.

kind tm  type.
kind ty  type.

type app      tm -> tm -> tm.
type abs      (tm -> tm) -> tm.
type c        tm.
type arrow    ty -> ty -> ty.
type i        ty.
type of       tm -> ty -> o.
type hastype  tm -> o.

of c i.
of (abs M) (arrow A B) :-
  pi x\ (of x A => of (M x) B).
of (app M N) B :-
  of M (arrow A B), of N A.

hastype M :- of M _.
