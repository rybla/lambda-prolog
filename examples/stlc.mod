% title: Simply-Typed λ-Calculus with Advanced Types
% tags: hoas, evaluation, stlc, type-preservation, higher-order
% summary: Full simply-typed lambda calculus with HOAS: base types, booleans,
%   pairs, sums (either), unit, recursion via fix, big-step call-by-value
%   evaluation, hypothetical typing contexts, and type preservation checking.

module stlc.

kind tm type.
kind ty type.

% Types
type unit_ty  ty.
type bool_ty  ty.
type int_ty   ty.
type prod_ty  ty -> ty -> ty.
type sum_ty   ty -> ty -> ty.
type arr_ty   ty -> ty -> ty.

% Term constructors
type unit_tm  tm.
type true_tm  tm.
type false_tm tm.
type int_tm   int -> tm.
type if_tm    tm -> tm -> tm -> tm.
type pair_tm  tm -> tm -> tm.
type fst_tm   tm -> tm.
type snd_tm   tm -> tm.
type inl_tm   ty -> tm -> tm.
type inr_tm   ty -> tm -> tm.
type case_tm  tm -> (tm -> tm) -> (tm -> tm) -> tm.
type abs_tm   ty -> (tm -> tm) -> tm.
type app_tm   tm -> tm -> tm.
type fix_tm   ty -> (tm -> tm) -> tm.

% Predicates
type typeof     tm -> ty -> o.
type eval       tm -> tm -> o.
type value      tm -> o.
type preserves  tm -> o.

% Values
value unit_tm.
value true_tm.
value false_tm.
value (int_tm _).
value (pair_tm V1 V2) :- value V1, value V2.
value (inl_tm _ V)    :- value V.
value (inr_tm _ V)    :- value V.
value (abs_tm _ _).

% Type system (hypothetical typing context via =>)
typeof unit_tm unit_ty.
typeof true_tm bool_ty.
typeof false_tm bool_ty.
typeof (int_tm _) int_ty.

typeof (if_tm C T E) Ty :-
  typeof C bool_ty,
  typeof T Ty,
  typeof E Ty.

typeof (pair_tm M N) (prod_ty A B) :-
  typeof M A,
  typeof N B.

typeof (fst_tm M) A :-
  typeof M (prod_ty A _).

typeof (snd_tm M) B :-
  typeof M (prod_ty _ B).

typeof (inl_tm B M) (sum_ty A B) :-
  typeof M A.

typeof (inr_tm A N) (sum_ty A B) :-
  typeof N B.

typeof (case_tm M L R) C :-
  typeof M (sum_ty A B),
  (pi x\ typeof x A => typeof (L x) C),
  (pi y\ typeof y B => typeof (R y) C).

typeof (abs_tm A Body) (arr_ty A B) :-
  pi x\ typeof x A => typeof (Body x) B.

typeof (app_tm M N) B :-
  typeof M (arr_ty A B),
  typeof N A.

typeof (fix_tm A Body) A :-
  pi x\ typeof x A => typeof (Body x) A.

% Big-step call-by-value evaluation
eval unit_tm unit_tm.
eval true_tm true_tm.
eval false_tm false_tm.
eval (int_tm N) (int_tm N).

eval (if_tm C T E) V :-
  eval C VC,
  eval_if VC T E V.

type eval_if tm -> tm -> tm -> tm -> o.
eval_if true_tm T _ V :- eval T V.
eval_if false_tm _ E V :- eval E V.

eval (pair_tm M N) (pair_tm V1 V2) :-
  eval M V1,
  eval N V2.

eval (fst_tm M) V1 :-
  eval M (pair_tm V1 _).

eval (snd_tm M) V2 :-
  eval M (pair_tm _ V2).

eval (inl_tm B M) (inl_tm B V) :-
  eval M V.

eval (inr_tm A N) (inr_tm A V) :-
  eval N V.

eval (case_tm M L R) V :-
  eval M VM,
  eval_case VM L R V.

type eval_case tm -> (tm -> tm) -> (tm -> tm) -> tm -> o.
eval_case (inl_tm _ V0) L _ V :- eval (L V0) V.
eval_case (inr_tm _ V0) _ R V :- eval (R V0) V.

eval (abs_tm A Body) (abs_tm A Body).

eval (app_tm M N) V :-
  eval M (abs_tm _ Body),
  eval N VN,
  eval (Body VN) V.

eval (fix_tm A Body) V :-
  eval (Body (fix_tm A Body)) V.

% Type preservation (Subject Reduction)
preserves M :-
  typeof M Ty,
  eval M V,
  typeof V Ty.

% ---------------------------------------------------------------------------
% Example queries:
%   ?- typeof (abs_tm int_ty (x\ x)) Ty.
%   ?- eval (app_tm (abs_tm int_ty (x\ x)) (int_tm 42)) V.
%   ?- preserves (app_tm (abs_tm int_ty (x\ x)) (int_tm 42)).
%   ?- eval (fst_tm (pair_tm (int_tm 10) true_tm)) V.
%   ?- eval (case_tm (inl_tm bool_ty (int_tm 7)) (x\ x) (y\ int_tm 0)) V.
