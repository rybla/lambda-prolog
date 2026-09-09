% title: Type inference
% tags: hoas, pi, implication
% summary: STLC type inference. pi introduces an object variable; => assumes
%   its type while inferring the body — binder mobility.

module typeinf.

kind tm  type.
kind ty  type.

type app     tm -> tm -> tm.
type abs     (tm -> tm) -> tm.
type arrow   ty -> ty -> ty.
type of      tm -> ty -> o.

of (abs M) (arrow A B) :-
  pi x\ (of x A => of (M x) B).
of (app M N) B :-
  of M (arrow A B), of N A.
