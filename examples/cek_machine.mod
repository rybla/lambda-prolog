% title: The CEK Abstract Machine
% tags: abstract-machine, cek, operational-semantics, continuations, environments
% summary: Implementation of the CEK (Control, Environment, Kontinuation) abstract
%   machine of Felleisen and Friedman. Evaluates higher-order functional programs
%   without term substitution by using explicit variable environments and
%   continuation stacks. Includes step transitions, machine run to completion,
%   and equivalence checking against standard big-step substitution evaluation.

module cek_machine.

% ============================================================================
% Syntax of the Source Language
% ============================================================================

kind exp type.

type cst_e   int -> exp.
type var_e   string -> exp.
type abs_e   string -> exp -> exp.
type app_e   exp -> exp -> exp.
type add_e   exp -> exp -> exp.

% ============================================================================
% Values, Environments, and Continuations
% ============================================================================

kind v_val type.
kind env_t type.
kind kont  type.

% Values in the CEK machine:
type v_int   int -> v_val.
% A closure pairs an un-substituted function (x, Body) with its lexical environment
type v_clos  string -> exp -> env_t -> v_val.

% Environment: list of bindings (name * v_val)
type env_nil  env_t.
type env_cons string -> v_val -> env_t -> env_t.

% Continuation frames (K):
% k_mt: empty continuation (halt)
type k_mt    kont.
% k_arg: evaluate argument N in environment E, then continue with K
type k_arg   exp -> env_t -> kont -> kont.
% k_fn: function evaluated to closure V; now evaluate argument and apply
type k_fn    v_val -> kont -> kont.
% k_add_r: evaluate right operand of addition
type k_add_r exp -> env_t -> kont -> kont.
% k_add_l: left operand evaluated to integer; add to incoming value
type k_add_l int -> kont -> kont.

% ============================================================================
% Machine State
% ============================================================================

kind control type.
type c_eval exp -> control.     % Evaluating an expression
type c_ret  v_val -> control.   % Returning a computed value

kind state type.
type cek_state control -> env_t -> kont -> state.

% ============================================================================
% Environment Operations
% ============================================================================

type env_lookup env_t -> string -> v_val -> o.

env_lookup (env_cons X V _) X V.
env_lookup (env_cons Y _ Rest) X V :-
  not (X = Y),
  env_lookup Rest X V.

% ============================================================================
% CEK Machine Step Transitions: state ⟶ state
% ============================================================================

type cek_step state -> state -> o.

% 1. Evaluate Constant: returns integer value
cek_step (cek_state (c_eval (cst_e N)) Env K)
         (cek_state (c_ret (v_int N)) Env K).

% 2. Evaluate Variable: looks up variable in lexical environment
cek_step (cek_state (c_eval (var_e X)) Env K)
         (cek_state (c_ret V) Env K) :-
  env_lookup Env X V.

% 3. Evaluate Abstraction: captures lexical environment into a closure
cek_step (cek_state (c_eval (abs_e X Body)) Env K)
         (cek_state (c_ret (v_clos X Body Env)) Env K).

% 4. Evaluate Application: start evaluating operator, save argument on K
cek_step (cek_state (c_eval (app_e M N)) Env K)
         (cek_state (c_eval M) Env (k_arg N Env K)).

% 5. Return function to k_arg: function is ready; now evaluate argument N
cek_step (cek_state (c_ret V) _ (k_arg N Env K))
         (cek_state (c_eval N) Env (k_fn V K)).

% 6. Return argument to k_fn: apply closure to argument value
cek_step (cek_state (c_ret W) _ (k_fn (v_clos X Body EnvClos) K))
         (cek_state (c_eval Body) (env_cons X W EnvClos) K).

% 7. Addition: evaluate left operand
cek_step (cek_state (c_eval (add_e E1 E2)) Env K)
         (cek_state (c_eval E1) Env (k_add_r E2 Env K)).

% 8. Return left to k_add_r: evaluate right operand
cek_step (cek_state (c_ret (v_int N1)) _ (k_add_r E2 Env K))
         (cek_state (c_eval E2) Env (k_add_l N1 K)).

% 9. Return right to k_add_l: compute sum and return
cek_step (cek_state (c_ret (v_int N2)) Env (k_add_l N1 K))
         (cek_state (c_ret (v_int Sum)) Env K) :-
  Sum is N1 + N2.

% ============================================================================
% Machine Execution to Halt
% ============================================================================

type cek_run   state -> v_val -> o.
type cek_eval  exp -> v_val -> o.

% Terminal state: returning a value to the empty continuation k_mt
cek_run (cek_state (c_ret V) _ k_mt) V :- !.

% Non-terminal step:
cek_run S FinalVal :-
  cek_step S S',
  cek_run S' FinalVal.

% Top-level evaluation of an expression in empty environment and empty continuation:
cek_eval E V :-
  cek_run (cek_state (c_eval E) env_nil k_mt) V.

% ============================================================================
% Big-Step Reference Evaluator (for equivalence checking)
% ============================================================================

type big_eval exp -> env_t -> v_val -> o.

big_eval (cst_e N) _ (v_int N).

big_eval (var_e X) Env V :-
  env_lookup Env X V.

big_eval (abs_e X Body) Env (v_clos X Body Env).

big_eval (add_e E1 E2) Env (v_int Sum) :-
  big_eval E1 Env (v_int N1),
  big_eval E2 Env (v_int N2),
  Sum is N1 + N2.

big_eval (app_e M N) Env Res :-
  big_eval M Env (v_clos X Body EnvClos),
  big_eval N Env W,
  big_eval Body (env_cons X W EnvClos) Res.

% Equivalence verification predicate:
type cek_sound exp -> o.
cek_sound E :-
  cek_eval E V1,
  big_eval E env_nil V2,
  V1 = V2.

% ============================================================================
% Example Queries
% ============================================================================

% Simple constant evaluation:
query succeeds ?
  cek_eval (cst_e 42) (v_int 42).

% Arithmetic addition: 10 + 20 = 30
query succeeds ?
  cek_eval (add_e (cst_e 10) (cst_e 20)) (v_int 30).

% Identity function application: (λx. x) 7 = 7
query succeeds ?
  cek_eval (app_e (abs_e "x" (var_e "x")) (cst_e 7)) (v_int 7).

% Higher-order application with lexical closure environment:
% ((λx. λy. x + y) 15) 25 = 40
query succeeds ?
  cek_eval
    (app_e
      (app_e (abs_e "x" (abs_e "y" (add_e (var_e "x") (var_e "y"))))
             (cst_e 15))
      (cst_e 25))
    (v_int 40).

% Equivalence check between CEK machine and big-step semantics:
query succeeds ?
  cek_sound
    (app_e
      (app_e (abs_e "x" (abs_e "y" (add_e (var_e "x") (var_e "y"))))
             (cst_e 100))
      (cst_e 200)).
