% title: Bidirectional Type Checking & Local Type Inference
% tags: bidirectional, type-inference, subsumption, local-inference, hoas
% summary: Bidirectional type checking system following Dunfield & Krishnaswami
%   and Pierce & Turner. Separates typing into Checking mode (Γ ⊢ e ⇐ τ) and
%   Synthesis/Inference mode (Γ ⊢ e ⇒ τ). Enables clean unannotated λ-abstractions,
%   first-class annotations, constructors (pairs, sums), let-bindings, and
%   subsumption with subtyping (e.g. Nat <: Int).

module bidirectional.

% ============================================================================
% Kinds and Types
% ============================================================================

kind ty type.
kind tm type.

% Types:
type unit_ty  ty.
type bool_ty  ty.
type nat_ty   ty.
type int_ty   ty.
type arr_ty   ty -> ty -> ty.
type prod_ty  ty -> ty -> ty.
type sum_ty   ty -> ty -> ty.

% ============================================================================
% Terms
% ============================================================================

% Base constants:
type unit_tm  tm.
type true_tm  tm.
type false_tm tm.
type nat_tm   int -> tm.
type int_tm   int -> tm.

% Unannotated lambda abstraction: λx. M (no type annotation required on binder!)
type lam_tm   (tm -> tm) -> tm.

% Term application: M N
type app_tm   tm -> tm -> tm.

% Type annotation: (M : T) mediates between synthesis and checking
type ann_tm   tm -> ty -> tm.

% Pairs and projections
type pair_tm  tm -> tm -> tm.
type fst_tm   tm -> tm.
type snd_tm   tm -> tm.

% Sum injections and case analysis
type inl_tm   tm -> tm.
type inr_tm   tm -> tm.
type case_tm  tm -> (tm -> tm) -> (tm -> tm) -> tm.

% Let binding: let x = M in N
type let_tm   tm -> (tm -> tm) -> tm.

% ============================================================================
% Subtyping Relation (S <: T)
% ============================================================================

type sub ty -> ty -> o.

% Reflexivity on base types
sub unit_ty unit_ty.
sub bool_ty bool_ty.
sub nat_ty nat_ty.
sub int_ty int_ty.

% Nat is a subtype of Int: Nat <: Int
sub nat_ty int_ty.

% Arrow subtyping (contravariant domain, covariant codomain)
sub (arr_ty S1 S2) (arr_ty T1 T2) :-
  sub T1 S1,
  sub S2 T2.

% Product subtyping (covariant)
sub (prod_ty S1 S2) (prod_ty T1 T2) :-
  sub S1 T1,
  sub S2 T2.

% Sum subtyping (covariant)
sub (sum_ty S1 S2) (sum_ty T1 T2) :-
  sub S1 T1,
  sub S2 T2.

% ============================================================================
% Bidirectional Type System
% ============================================================================

% Synth mode: synthesize / infer the type from the term structure (Γ ⊢ e ⇒ τ)
type synth_ty tm -> ty -> o.

% Check mode: verify the term against an incoming expected type (Γ ⊢ e ⇐ τ)
type check_ty tm -> ty -> o.

% Context assumption for variables in scope
type has_ty   tm -> ty -> o.

% ----------------------------------------------------------------------------
% Synthesis Rules (Γ ⊢ e ⇒ τ)
% ----------------------------------------------------------------------------

% Variables look up their assumed type in the hypothetical context
synth_ty X Ty :-
  has_ty X Ty, !.

% Literals have known types:
synth_ty unit_tm unit_ty.
synth_ty true_tm bool_ty.
synth_ty false_tm bool_ty.
synth_ty (nat_tm N) nat_ty :- N >= 0.
synth_ty (int_tm _) int_ty.

% Annotated term: (M : T) synthesizes T if M checks against T
% Γ ⊢ M ⇐ T
% ------------- (Synth-Ann)
% Γ ⊢ (M : T) ⇒ T
synth_ty (ann_tm M T) T :-
  check_ty M T.

% Application:
% Γ ⊢ M ⇒ A -> B    Γ ⊢ N ⇐ A
% --------------------------- (Synth-App)
%        Γ ⊢ M N ⇒ B
synth_ty (app_tm M N) B :-
  synth_ty M ArrTy,
  ArrTy = arr_ty A B,
  check_ty N A.

% Projections synthesize types from product terms:
synth_ty (fst_tm M) A :-
  synth_ty M (prod_ty A _).

synth_ty (snd_tm M) B :-
  synth_ty M (prod_ty _ B).

% Let-binding: infer type of definition, then check or synthesize body
synth_ty (let_tm Def Body) Ty :-
  synth_ty Def DefTy,
  (pi x\ (has_ty x DefTy => synth_ty (Body x) Ty)).

% ----------------------------------------------------------------------------
% Checking Rules (Γ ⊢ e ⇐ τ)
% ----------------------------------------------------------------------------

% Lambda abstraction checking against arrow type:
% Parameter type A comes from the expected type; no annotation needed on λ!
%
%   Γ, x:A ⊢ M ⇐ B
% ------------------ (Check-Abs)
%  Γ ⊢ (λx. M) ⇐ A -> B
check_ty (lam_tm Body) (arr_ty A B) :-
  pi x\ (has_ty x A => check_ty (Body x) B).

% Pair checking against product type:
% Γ ⊢ M ⇐ A    Γ ⊢ N ⇐ B
% ---------------------- (Check-Pair)
%   Γ ⊢ (M, N) ⇐ A × B
check_ty (pair_tm M N) (prod_ty A B) :-
  check_ty M A,
  check_ty N B.

% Sum checking:
check_ty (inl_tm M) (sum_ty A _) :-
  check_ty M A.

check_ty (inr_tm N) (sum_ty _ B) :-
  check_ty N B.

% Case analysis checking:
check_ty (case_tm M L R) C :-
  synth_ty M (sum_ty A B),
  (pi x\ (has_ty x A => check_ty (L x) C)),
  (pi y\ (has_ty y B => check_ty (R y) C)).

% Let-binding checking:
check_ty (let_tm Def Body) Expected :-
  synth_ty Def DefTy,
  (pi x\ (has_ty x DefTy => check_ty (Body x) Expected)).

% Subsumption rule (Mode switch from check to synth):
% If term M can synthesize type S, and S is a subtype of expected type T,
% then M checks against T.
%
%  Γ ⊢ M ⇒ S    S <: T
% -------------------- (Subsumption)
%      Γ ⊢ M ⇐ T
check_ty M Expected :-
  synth_ty M Inferred,
  sub Inferred Expected.

% ============================================================================
% Example Queries
% ============================================================================

% Checking unannotated identity function against Int -> Int:
query succeeds ?
  check_ty (lam_tm (x\ x)) (arr_ty int_ty int_ty).

% Higher-order unannotated function:
% λf. λx. f x  checked against (Int -> Bool) -> Int -> Bool
query succeeds ?
  check_ty (lam_tm (f\ lam_tm (x\ app_tm f x)))
           (arr_ty (arr_ty int_ty bool_ty) (arr_ty int_ty bool_ty)).

% Subsumption: Nat <: Int allows a Nat term to be checked where Int is expected
query succeeds ?
  check_ty (nat_tm 5) int_ty.

% Unannotated function accepting Nat and returning Int:
% λx. x checked against Nat -> Int succeeds via subsumption on body!
query succeeds ?
  check_ty (lam_tm (x\ x)) (arr_ty nat_ty int_ty).

% Synthesis using explicit top-level annotation:
query succeeds ?
  synth_ty (ann_tm (lam_tm (x\ x)) (arr_ty int_ty int_ty))
           (arr_ty int_ty int_ty).

% Unannotated pair checking:
query succeeds ?
  check_ty (pair_tm (nat_tm 3) true_tm) (prod_ty int_ty bool_ty).

% Let-binding with inference:
query succeeds ?
  check_ty (let_tm (nat_tm 10) (n\ pair_tm n true_tm))
           (prod_ty int_ty bool_ty).

% Sum type injection checking:
query succeeds ?
  check_ty (inl_tm (nat_tm 42)) (sum_ty int_ty bool_ty).
