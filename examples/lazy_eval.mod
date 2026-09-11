% title: Call-by-Need & Lazy Evaluation (Launchbury's Semantics)
% tags: lazy-evaluation, call-by-need, heap, thunks, memoization, sharing
% summary: Call-by-need lazy operational semantics based on Launchbury's natural
%   semantics for lazy evaluation. Models sharing and memoization via a heap of
%   suspended thunks. When a shared variable is demanded, its thunk is evaluated
%   and the heap is updated in-place with the normalized value, ensuring shared
%   expressions are computed at most once.

module lazy_eval.

% ============================================================================
% Syntax of Lazy Expressions
% ============================================================================

kind lexp type.

type l_num    int -> lexp.
type l_var    int -> lexp.               % Variable reference by heap address
type l_add    lexp -> lexp -> lexp.
type l_lam    (lexp -> lexp) -> lexp.    % HOAS abstraction
type l_app    lexp -> lexp -> lexp.
type l_let    lexp -> (lexp -> lexp) -> lexp. % let x = E1 in E2

% ============================================================================
% Heap and Values
% ============================================================================

kind lval type.
type v_num  int -> lval.
type v_lam  (lexp -> lexp) -> lval.

kind hentry type.
type e_thunk lexp -> hentry.
type e_val   lval -> hentry.

kind hbinding type.
type hbind int -> hentry -> hbinding.

type heap list hbinding.

% ============================================================================
% Heap Operations
% ============================================================================

type heap_lookup list hbinding -> int -> hentry -> o.
type heap_update list hbinding -> int -> hentry -> list hbinding -> o.
type heap_alloc  list hbinding -> hentry -> int -> list hbinding -> o.

heap_lookup (hbind Addr E :: _) Addr E.
heap_lookup (_ :: Rest) Addr E :-
  heap_lookup Rest Addr E.

% Update heap entry at Addr with new entry E:
heap_update (hbind Addr _ :: Rest) Addr E (hbind Addr E :: Rest).
heap_update (B :: Rest) Addr E (B :: OutRest) :-
  heap_update Rest Addr E OutRest.

type heap_len list hbinding -> int -> o.
heap_len nil 0.
heap_len (_ :: Rest) N :-
  heap_len Rest M,
  N is M + 1.

% Allocate new entry at next fresh address (Len + 1):
heap_alloc H E NextAddr (hbind NextAddr E :: H) :-
  heap_len H Len,
  NextAddr is Len + 1.

% ============================================================================
% Call-by-Need Evaluation: eval_lazy InHeap Exp OutHeap Val
% ============================================================================

type eval_lazy list hbinding -> lexp -> list hbinding -> lval -> o.

% 1. Numbers evaluate immediately to values:
eval_lazy H (l_num N) H (v_num N).

% 2. Abstractions evaluate immediately to functional values:
eval_lazy H (l_lam Body) H (v_lam Body).

% 3. Variable lookup with memoization (Launchbury's Var rule):
% If the heap cell is already evaluated, return the cached value (no recomputation!)
eval_lazy H (l_var Addr) H V :-
  heap_lookup H Addr (e_val V), !.

% If the heap cell contains an unevaluated thunk, evaluate it and UPDATE the heap!
eval_lazy InH (l_var Addr) OutH V :-
  heap_lookup InH Addr (e_thunk Exp),
  eval_lazy InH Exp MidH V,
  heap_update MidH Addr (e_val V) OutH.

% 4. Let binding (Heap allocation):
% Allocate a suspended thunk for E1 in the heap, pass fresh heap address to Body.
eval_lazy InH (l_let E1 Body) OutH V :-
  heap_alloc InH (e_thunk E1) Addr MidH,
  eval_lazy MidH (Body (l_var Addr)) OutH V.

% 5. Application:
% Evaluate function to abstraction, allocate argument thunk in heap, apply body.
eval_lazy InH (l_app M N) OutH V :-
  eval_lazy InH M MidH1 (v_lam Body),
  heap_alloc MidH1 (e_thunk N) Addr MidH2,
  eval_lazy MidH2 (Body (l_var Addr)) OutH V.

% 6. Addition: demands both operands to numeric values
eval_lazy InH (l_add E1 E2) OutH (v_num Sum) :-
  eval_lazy InH E1 MidH1 (v_num N1),
  eval_lazy MidH1 E2 MidH2 (v_num N2),
  Sum is N1 + N2,
  OutH = MidH2.

% Top-level lazy evaluation from empty heap:
type run_lazy lexp -> lval -> o.
run_lazy E V :-
  eval_lazy nil E _ V.

% Check that an address in the final heap is marked evaluated (memoized):
type is_memoized list hbinding -> int -> o.
is_memoized H Addr :-
  heap_lookup H Addr (e_val _).

% ============================================================================
% Example Queries & Sharing Verification
% ============================================================================

% Simple constant evaluation:
query succeeds ?
  run_lazy (l_num 42) (v_num 42).

% Arithmetic addition: 10 + 20 = 30
query succeeds ?
  run_lazy (l_add (l_num 10) (l_num 20)) (v_num 30).

% Let binding: let x = 5 in x + x = 10
query succeeds ?
  run_lazy (l_let (l_num 5) (x\ l_add x x)) (v_num 10).

% Sharing and Memoization verification:
% let x = (10 + 20) in (x + x)
% Verifies that address 1 in the final heap contains (e_val (v_num 30)),
% confirming that (10 + 20) was memoized after the first access.
query succeeds ?
  eval_lazy nil (l_let (l_add (l_num 10) (l_num 20)) (x\ l_add x x)) FinalH (v_num 60),
  is_memoized FinalH 1.

% Higher-order lazy application:
% (λf. f 5) (λx. x + x)
query succeeds ?
  run_lazy
    (l_app (l_lam (f\ l_app f (l_num 5)))
           (l_lam (x\ l_add x x)))
    (v_num 10).
