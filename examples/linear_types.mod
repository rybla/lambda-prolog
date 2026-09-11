% title: Linear and Substructural Type System
% tags: linear-logic, substructural, resource-tracking, context-splitting
% summary: A linear type system based on Girard's linear logic and Wadler's
%   "Linear Types Can Change the World". Enforces resource tracking by ensuring
%   that linear values (capabilities, file handles, channels) are consumed
%   exactly once. Demonstrates context consumption, linear functions (A ⊸ B),
%   multiplicative tensor pairs (A ⊗ B), and prevention of double-spend and leaks.

module linear_types.

% ============================================================================
% Kinds and Types
% ============================================================================

kind lty type.
kind ltm type.

% Linear types:
type base_lty   string -> lty.
type handle_lty lty.            % Linear resource capability (e.g., file handle)
type coin_lty   lty.            % Linear token/currency (must not be duplicated or leaked)

% Multiplicative linear function: A ⊸ B
type lolli      lty -> lty -> lty.

% Multiplicative tensor product: A ⊗ B (both components must be consumed)
type tensor_ty  lty -> lty -> lty.

% Unrestricted / exponential type: !A (can be freely duplicated or dropped)
type bang_ty    lty -> lty.

% ============================================================================
% Linear Terms
% ============================================================================

% Base resources
type token      string -> ltm.
type handle     int -> ltm.

% Linear lambda abstraction: λx:A. M
type llam       lty -> (ltm -> ltm) -> ltm.

% Linear function application: M N
type lapp       ltm -> ltm -> ltm.

% Tensor pair construction: M ⊗ N
type pair_ltm   ltm -> ltm -> ltm.

% Tensor elimination: let x ⊗ y = M in N
type unpair_ltm ltm -> (ltm -> ltm -> ltm) -> ltm.

% Resource consumer: consumes a handle/token and produces an unrestricted result
type close_h    ltm -> ltm.
type spend_coin ltm -> ltm.
type done_ltm   ltm.

% ============================================================================
% Context Management and Consumption
% ============================================================================

% A linear context is represented as a list of pairs (pr Var Type).
% lin_of InCtx Term Type OutCtx:
% Typechecks Term against Type, consuming the required resources from InCtx
% and returning the remaining unconsumed resources in OutCtx.

kind res_entry type.
type rentry ltm -> lty -> res_entry.

type lin_of      list res_entry -> ltm -> lty -> list res_entry -> o.
type is_empty    list res_entry -> o.
type extract_res ltm -> lty -> list res_entry -> list res_entry -> o.

is_empty nil.

% Extract a specific variable binding from the linear context (exact consumption):
extract_res X T (rentry X T :: Rest) Rest.
extract_res X T (Y :: Rest) (Y :: OutRest) :-
  extract_res X T Rest OutRest.

% ============================================================================
% Linear Typing Rules
% ============================================================================

% Variable Rule (Linear axiom):
% Variable X of type T is consumed from the context.
lin_of In (token S) (base_lty S) In.
lin_of In done_ltm (base_lty "unit") In.

% Linear variable lookup: consumes exactly this variable from the context
lin_of In X T Out :-
  extract_res X T In Out.

type not_member  ltm -> list res_entry -> o.

not_member _ nil.
not_member X (rentry Y _ :: Rest) :-
  not (X = Y),
  not_member X Rest.

% Linear Abstraction (⊸ Intro):
% Γ, x:A ⊢ M : B ⊣ Γ'
% Introduce fresh linear variable x:A into context. The variable x MUST be
% consumed during typechecking of Body (i.e. x is not in Mid).
lin_of In (llam A Body) (lolli A B) Out :-
  pi x\ (
    lin_of (rentry x A :: In) (Body x) B Mid,
    not_member x Mid,
    Out = Mid
  ).

% Linear Application (⊸ Elim):
% Γ ⊢ M : A ⊸ B ⊣ Δ    Δ ⊢ N : A ⊣ Θ
% -----------------------------------
%           Γ ⊢ M N : B ⊣ Θ
lin_of In (lapp M N) B Out :-
  lin_of In M (lolli A B) Mid,
  lin_of Mid N A Out.

% Tensor Introduction (⊗ Intro):
% Resources are threaded: M consumes from In to Mid, N consumes from Mid to Out.
lin_of In (pair_ltm M N) (tensor_ty A B) Out :-
  lin_of In M A Mid,
  lin_of Mid N B Out.

% Tensor Elimination (⊗ Elim):
% let x ⊗ y = M in N
% Both x:A and y:B are added to the linear context and must be consumed by Body.
lin_of In (unpair_ltm M Body) C Out :-
  lin_of In M (tensor_ty A B) Mid,
  pi x\ pi y\ (
    lin_of (rentry x A :: rentry y B :: Mid) (Body x y) C Mid2,
    not_member x Mid2,
    not_member y Mid2,
    Out = Mid2
  ).

% Resource consumers:
% close_h consumes a handle_lty resource from context
lin_of In (close_h H) (base_lty "unit") Out :-
  lin_of In H handle_lty Out.

% spend_coin consumes a coin_lty resource from context
lin_of In (spend_coin C) (base_lty "receipt") Out :-
  lin_of In C coin_lty Out.

% Whole-program linear closed term checking:
% Checks that M produces T and leaves NO leftover linear resources.
type lin_closed ltm -> lty -> o.
lin_closed M T :-
  lin_of nil M T Out,
  is_empty Out.

% ============================================================================
% Example Queries & Resource Safety Verification
% ============================================================================

% Linear Identity: λx. x is a valid linear function A ⊸ A:
query succeeds ?
  lin_closed (llam coin_lty (c\ c)) (lolli coin_lty coin_lty).

% Correctly spending a coin produces a receipt with no leaks:
query succeeds ?
  lin_closed (llam coin_lty (c\ spend_coin c))
             (lolli coin_lty (base_lty "receipt")).

% Tensor pair of resources consumed via unpairing and returned as pair of receipts:
% λp. let c1 ⊗ c2 = p in (spend_coin c1) ⊗ (spend_coin c2)
query succeeds ?
  lin_closed
    (llam (tensor_ty coin_lty coin_lty)
      (p\ unpair_ltm p (c1\ c2\ pair_ltm (spend_coin c1) (spend_coin c2))))
    (lolli (tensor_ty coin_lty coin_lty)
           (tensor_ty (base_lty "receipt") (base_lty "receipt"))).

% Resource Leak Detection (Failure):
% A linear function that accepts a coin but ignores it must FAIL:
query fails ?
  lin_closed (llam coin_lty (_\ done_ltm)) (lolli coin_lty (base_lty "unit")).

% Double-Spend Detection (Failure):
% Attempting to spend the same coin twice must FAIL:
query fails ?
  lin_closed
    (llam coin_lty (c\ pair_ltm (spend_coin c) (spend_coin c)))
    (lolli coin_lty (tensor_ty (base_lty "receipt") (base_lty "receipt"))).
