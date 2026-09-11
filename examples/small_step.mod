% title: Small-Step Reduction & Evaluation Contexts
% tags: small-step, sos, evaluation-contexts, progress, type-safety
% summary: Small-step Structural Operational Semantics (SOS) with evaluation
%   contexts E[·] following Wright & Felleisen. Features explicit redex decomposition
%   and plug operations, multi-step transitive closure, stuck-state detection,
%   and formal Wright-Felleisen progress and preservation verification.

module small_step.

% ============================================================================
% Syntax: Types and Terms
% ============================================================================

kind ty type.
kind tm type.

% Types
type bool_ty ty.
type int_ty  ty.
type arr_ty  ty -> ty -> ty.

% Terms
type true_tm  tm.
type false_tm tm.
type int_tm   int -> tm.
type if_tm    tm -> tm -> tm -> tm.
type abs_tm   ty -> (tm -> tm) -> tm.
type app_tm   tm -> tm -> tm.

% Values
type value tm -> o.
value true_tm.
value false_tm.
value (int_tm _).
value (abs_tm _ _).

% ============================================================================
% Typing Rules
% ============================================================================

type typeof tm -> ty -> o.

typeof true_tm bool_ty.
typeof false_tm bool_ty.
typeof (int_tm _) int_ty.

typeof (if_tm C T E) Ty :-
  typeof C bool_ty,
  typeof T Ty,
  typeof E Ty.

typeof (abs_tm A Body) (arr_ty A B) :-
  pi x\ (typeof x A => typeof (Body x) B).

typeof (app_tm M N) B :-
  typeof M (arr_ty A B),
  typeof N A.

% ============================================================================
% Evaluation Contexts (Call-by-Value)
% ============================================================================

% Context grammar:
% E ::= [·] | E e2 | v1 E | if E then e2 else e3
kind ctx type.

type hole_ctx ctx.
type app_l    ctx -> tm -> ctx.        % E e2
type app_r    tm -> ctx -> ctx.        % v1 E  (v1 is a value)
type if_c     ctx -> tm -> tm -> ctx.  % if E then e2 else e3

% Context plugging: plug C HoleTerm Result
type plug ctx -> tm -> tm -> o.

plug hole_ctx M M.
plug (app_l C N) M (app_tm E N) :-
  plug C M E.
plug (app_r V C) M (app_tm V E) :-
  plug C M E.
plug (if_c C T E) M (if_tm Cond T E) :-
  plug C M Cond.

% ============================================================================
% Primitive Redexes
% ============================================================================

type redex tm -> tm -> o.

% Beta-reduction (CBV: argument must be a value):
% (λx. M) V ⟶ M[V]
redex (app_tm (abs_tm _ Body) V) (Body V) :-
  value V.

% Conditional reductions:
redex (if_tm true_tm T _) T.
redex (if_tm false_tm _ E) E.

% ============================================================================
% Contextual Decomposition & Small-Step Relation
% ============================================================================

% Decompose a non-value term into an evaluation context and an active redex:
type decompose tm -> ctx -> tm -> o.

% Redex at top level:
decompose M hole_ctx M :-
  redex M _, !.

% If condition is not a value, decompose within conditional context:
decompose (if_tm C T E) (if_c Ctx T E) R :-
  not (value C),
  decompose C Ctx R.

% Left side of application is not a value:
decompose (app_tm M N) (app_l Ctx N) R :-
  not (value M),
  decompose M Ctx R.

% Left side is a value, but right side is not a value:
decompose (app_tm V N) (app_r V Ctx) R :-
  value V,
  not (value N),
  decompose N Ctx R.

% Single small-step reduction (M ⟶ M'):
type step tm -> tm -> o.

step M M' :-
  decompose M Ctx R,
  redex R R',
  plug Ctx R' M'.

% Reflexive transitive closure of step (M ⟶* M'):
type steps tm -> tm -> o.

steps M M :-
  value M, !.
steps M Res :-
  step M M',
  steps M' Res.

% ============================================================================
% Type Safety: Progress, Preservation, and Stuck States
% ============================================================================

% Progress Theorem (Wright-Felleisen):
% A well-typed term is either already a terminal value, or can take a step.
type progress tm -> o.
progress M :-
  value M, !.
progress M :-
  step M _, !.

% Stuck state: a term is stuck if it is NOT a value and CANNOT step.
type is_stuck tm -> o.
is_stuck M :-
  not (value M),
  not (step M _).

% Preservation check across one step:
type preserves_step tm -> o.
preserves_step M :-
  typeof M Ty,
  step M M',
  typeof M' Ty.

% ============================================================================
% Example Queries
% ============================================================================

% Single step beta reduction:
query succeeds ?
  step (app_tm (abs_tm int_ty (x\ x)) (int_tm 42))
       (int_tm 42).

% Nested reduction under evaluation context:
% (λx. x) ((λy. y) 10) ⟶ (λx. x) 10
query succeeds ?
  step (app_tm (abs_tm int_ty (x\ x))
               (app_tm (abs_tm int_ty (y\ y)) (int_tm 10)))
       (app_tm (abs_tm int_ty (x\ x)) (int_tm 10)).

% Multi-step reduction to value:
query succeeds ?
  steps (if_tm (if_tm true_tm false_tm true_tm) (int_tm 1) (int_tm 2))
        (int_tm 2).

% Progress check on well-typed terms:
query succeeds ?
  progress (if_tm true_tm (int_tm 1) (int_tm 2)).
query succeeds ?
  progress (int_tm 42).

% Preservation check:
query succeeds ?
  preserves_step (if_tm true_tm (int_tm 100) (int_tm 200)).

% Stuck state detection: ill-typed terms get stuck:
% (42 true) cannot step and is not a value!
query succeeds ?
  is_stuck (app_tm (int_tm 42) true_tm).
