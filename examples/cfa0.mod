% title: 0-CFA Control Flow Analysis for Higher-Order Programs
% tags: cfa, static-analysis, abstract-interpretation, flow-analysis, call-graph
% summary: 0-CFA (0th-order Control Flow Analysis) for higher-order functional
%   programs formulated as abstract interpretation. Computes abstract closure
%   values, models closure environments to capture lexical variable flows across
%   nested higher-order applications, and statically reconstructs the interprocedural
%   call graph.

module cfa0.

% ============================================================================
% Labeled Syntax for 0-CFA
% ============================================================================

kind lab   type.
kind c_exp type.

type lab_id  string -> lab.

% Labeled expressions:
type c_num   int -> lab -> c_exp.
type c_var   string -> lab -> c_exp.
% Labeled abstraction: lam X Body LamLabel
type c_lam   string -> c_exp -> lab -> c_exp.
% Labeled application: app Func Arg AppLabel
type c_app   c_exp -> c_exp -> lab -> c_exp.
% Conditional expression with multiple flow paths:
type c_if    c_exp -> c_exp -> c_exp -> lab -> c_exp.

% ============================================================================
% Abstract Values and Closure Environments
% ============================================================================

kind abs_val type.
kind abs_env type.

type a_int   abs_val.
% Abstract closure: pairs binder name, body AST, captured environment, and source label
type a_clos  string -> c_exp -> abs_env -> lab -> abs_val.

% Environment: list of abstract variable bindings
type env_nil  abs_env.
type env_cons string -> abs_val -> abs_env -> abs_env.

type env_lookup abs_env -> string -> abs_val -> o.

env_lookup (env_cons X V _) X V.
env_lookup (env_cons Y _ Rest) X V :-
  not (X = Y),
  env_lookup Rest X V.

% ============================================================================
% 0-CFA Evaluation (Abstract Interpretation)
% ============================================================================

% cfa_eval Environment Expression ResultAbstractValue
type cfa_eval abs_env -> c_exp -> abs_val -> o.

% Constants evaluate to abstract integer value:
cfa_eval _ (c_num _ _) a_int.

% Variable occurrences look up their abstract values from lexical environment:
cfa_eval Env (c_var X _) V :-
  env_lookup Env X V.

% Lambda abstractions evaluate to closures capturing the current lexical environment:
cfa_eval Env (c_lam X Body L) (a_clos X Body Env L).

% Conditionals: control flow merges both branches (flow-insensitive join):
cfa_eval Env (c_if _ Then Else _) V :-
  cfa_eval Env Then V ; cfa_eval Env Else V.

% Applications (Call sites):
% Evaluate operator to an abstract closure, evaluate operand to abstract value,
% extend captured environment, and evaluate closure body.
cfa_eval Env (c_app E1 E2 _) Res :-
  cfa_eval Env E1 (a_clos X Body ClosEnv _),
  cfa_eval Env E2 ArgVal,
  cfa_eval (env_cons X ArgVal ClosEnv) Body Res.

% Top-level evaluation in empty environment:
type cfa_run c_exp -> abs_val -> o.
cfa_run E V :-
  cfa_eval env_nil E V.

% ============================================================================
% Call Graph Construction
% ============================================================================

% calls Exp AppSiteLabel TargetLambdaLabel:
% Holds if the application at AppSiteLabel can call the function TargetLambdaLabel.
type calls abs_env -> c_exp -> lab -> lab -> o.

calls Env (c_app E1 E2 AppL) AppL LamL :-
  cfa_eval Env E1 (a_clos _ _ _ LamL).

% Subterm search for call edges across the AST:
calls Env (c_lam _ Body _) AppL LamL :-
  calls Env Body AppL LamL.

calls Env (c_app E1 _ _) AppL LamL :-
  calls Env E1 AppL LamL.

calls Env (c_app _ E2 _) AppL LamL :-
  calls Env E2 AppL LamL.

calls Env (c_if C T E _) AppL LamL :-
  calls Env C AppL LamL ; calls Env T AppL LamL ; calls Env E AppL LamL.

type call_graph c_exp -> lab -> lab -> o.
call_graph E AppL LamL :-
  calls env_nil E AppL LamL.

% ============================================================================
% Example Queries
% ============================================================================

% Sample program 1: Identity application
% ((λx. x)^lam_id 42)^app_1
% Verify that lam_id is called at app_1
query succeeds ?
  E = (c_app (c_lam "x" (c_var "x" (lab_id "l_x")) (lab_id "lam_id"))
             (c_num 42 (lab_id "l_42"))
             (lab_id "app_1")),
  call_graph E (lab_id "app_1") (lab_id "lam_id").

% Sample program 2: Higher-order function passing
% apply = λf. λy. f y
% id = λx. x
% Expression: (apply id) 99
% Verify that evaluating full expression yields abstract integer
query succeeds ?
  E_id = (c_lam "x" (c_var "x" (lab_id "x")) (lab_id "lam_id")),
  E_apply =
    (c_lam "f"
      (c_lam "y"
        (c_app (c_var "f" (lab_id "f_call"))
               (c_var "y" (lab_id "y_arg"))
               (lab_id "inner_app"))
        (lab_id "lam_inner"))
      (lab_id "lam_apply")),
  E_full = (c_app (c_app E_apply E_id (lab_id "call_apply"))
                  (c_num 99 (lab_id "arg_99"))
                  (lab_id "top_app")),
  cfa_run E_full a_int.

% Sample program 3: Conditional flow join (multiple targets at one call site)
% if cond then (λx. x)^lam_1 else (λy. y)^lam_2
% When applied, the call site can target BOTH lam_1 and lam_2!
query succeeds ?
  F1 = (c_lam "x" (c_var "x" (lab_id "x")) (lab_id "lam_1")),
  F2 = (c_lam "y" (c_var "y" (lab_id "y")) (lab_id "lam_2")),
  Branch = (c_if (c_num 1 (lab_id "c")) F1 F2 (lab_id "if_site")),
  Call = (c_app Branch (c_num 5 (lab_id "arg")) (lab_id "call_branch")),
  call_graph Call (lab_id "call_branch") (lab_id "lam_1").

query succeeds ?
  F1 = (c_lam "x" (c_var "x" (lab_id "x")) (lab_id "lam_1")),
  F2 = (c_lam "y" (c_var "y" (lab_id "y")) (lab_id "lam_2")),
  Branch = (c_if (c_num 1 (lab_id "c")) F1 F2 (lab_id "if_site")),
  Call = (c_app Branch (c_num 5 (lab_id "arg")) (lab_id "call_branch")),
  call_graph Call (lab_id "call_branch") (lab_id "lam_2").
