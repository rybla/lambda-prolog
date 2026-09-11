% title: Hoare Logic & Dijkstra's Weakest Precondition Calculus
% tags: hoare-logic, program-verification, weakest-precondition, vcg, formal-methods
% summary: Axiomatic program verification for an imperative While language using
%   Hoare triples {P} C {Q} and Dijkstra's backward predicate transformer
%   (Weakest Precondition wp). Automatically generates and discharges verification
%   conditions (VCs) for loop invariants, assignment backward substitution,
%   and state assertions.

module hoare_logic.

% ============================================================================
% Arithmetic Expressions and Boolean Conditions
% ============================================================================

kind aexpr type.
kind bexpr type.

type a_num  int -> aexpr.
type a_var  string -> aexpr.
type a_plus aexpr -> aexpr -> aexpr.
type a_sub  aexpr -> aexpr -> aexpr.
type a_mul  aexpr -> aexpr -> aexpr.

type b_true  bexpr.
type b_false bexpr.
type b_eq    aexpr -> aexpr -> bexpr.
type b_lt    aexpr -> aexpr -> bexpr.
type b_le    aexpr -> aexpr -> bexpr.
type b_gt    aexpr -> aexpr -> bexpr.
type b_ge    aexpr -> aexpr -> bexpr.
type b_not   bexpr -> bexpr.
type b_and   bexpr -> bexpr -> bexpr.

% ============================================================================
% Assertions (First-Order State Formulas)
% ============================================================================

kind assert type.

type p_true  assert.
type p_false assert.
type p_eq    aexpr -> aexpr -> assert.
type p_lt    aexpr -> aexpr -> assert.
type p_le    aexpr -> aexpr -> assert.
type p_gt    aexpr -> aexpr -> assert.
type p_ge    aexpr -> aexpr -> assert.
type p_and   assert -> assert -> assert.
type p_or    assert -> assert -> assert.
type p_not   assert -> assert.
type p_imp   assert -> assert -> assert.

% Conversion of Boolean condition to assertion:
type b_to_assert bexpr -> assert -> o.
b_to_assert b_true p_true.
b_to_assert b_false p_false.
b_to_assert (b_eq E1 E2) (p_eq E1 E2).
b_to_assert (b_lt E1 E2) (p_lt E1 E2).
b_to_assert (b_le E1 E2) (p_le E1 E2).
b_to_assert (b_gt E1 E2) (p_gt E1 E2).
b_to_assert (b_ge E1 E2) (p_ge E1 E2).
b_to_assert (b_not B) (p_not P) :- b_to_assert B P.
b_to_assert (b_and B1 B2) (p_and P1 P2) :-
  b_to_assert B1 P1,
  b_to_assert B2 P2.

% ============================================================================
% Commands (While Language)
% ============================================================================

kind cmd type.

type c_skip   cmd.
type c_assign string -> aexpr -> cmd.
type c_seq    cmd -> cmd -> cmd.
type c_if     bexpr -> cmd -> cmd -> cmd.
% While loop annotated with loop invariant Inv: while B do {Inv} C
type c_while  bexpr -> assert -> cmd -> cmd.

% ============================================================================
% Substitution on Expressions and Assertions: subst_a Var Val In Out
% ============================================================================

type subst_e string -> aexpr -> aexpr -> aexpr -> o.

subst_e X Val (a_var X) Val :- !.
subst_e _ _ (a_var Y) (a_var Y).
subst_e _ _ (a_num N) (a_num N).
subst_e X Val (a_plus E1 E2) (a_plus E1' E2') :-
  subst_e X Val E1 E1',
  subst_e X Val E2 E2'.
subst_e X Val (a_sub E1 E2) (a_sub E1' E2') :-
  subst_e X Val E1 E1',
  subst_e X Val E2 E2'.
subst_e X Val (a_mul E1 E2) (a_mul E1' E2') :-
  subst_e X Val E1 E1',
  subst_e X Val E2 E2'.

type subst_a string -> aexpr -> assert -> assert -> o.

subst_a _ _ p_true p_true.
subst_a _ _ p_false p_false.
subst_a X Val (p_eq E1 E2) (p_eq E1' E2') :-
  subst_e X Val E1 E1',
  subst_e X Val E2 E2'.
subst_a X Val (p_lt E1 E2) (p_lt E1' E2') :-
  subst_e X Val E1 E1',
  subst_e X Val E2 E2'.
subst_a X Val (p_le E1 E2) (p_le E1' E2') :-
  subst_e X Val E1 E1',
  subst_e X Val E2 E2'.
subst_a X Val (p_gt E1 E2) (p_gt E1' E2') :-
  subst_e X Val E1 E1',
  subst_e X Val E2 E2'.
subst_a X Val (p_ge E1 E2) (p_ge E1' E2') :-
  subst_e X Val E1 E1',
  subst_e X Val E2 E2'.
subst_a X Val (p_and P1 P2) (p_and P1' P2') :-
  subst_a X Val P1 P1',
  subst_a X Val P2 P2'.
subst_a X Val (p_or P1 P2) (p_or P1' P2') :-
  subst_a X Val P1 P1',
  subst_a X Val P2 P2'.
subst_a X Val (p_not P) (p_not P') :-
  subst_a X Val P P'.
subst_a X Val (p_imp P1 P2) (p_imp P1' P2') :-
  subst_a X Val P1 P1',
  subst_a X Val P2 P2'.

% ============================================================================
% Dijkstra's Weakest Precondition Transformer (wp) & VCG
% ============================================================================

% vcg Command Postcondition Precondition VerificationConditionsList
type vcg cmd -> assert -> assert -> list assert -> o.

% 1. Skip rule: wp(skip, Q) = Q
vcg c_skip Q Q nil.

% 2. Assignment rule: wp(x := e, Q) = Q[x ↦ e]
vcg (c_assign X E) Q Pre nil :-
  subst_a X E Q Pre.

% 3. Sequence rule: wp(C1; C2, Q) = wp(C1, wp(C2, Q))
vcg (c_seq C1 C2) Q Pre VCs :-
  vcg C2 Q MidMid VCs2,
  vcg C1 MidMid Pre VCs1,
  is_append VCs1 VCs2 VCs.

type is_append list A -> list A -> list A -> o.
is_append nil L L.
is_append (X :: Xs) Ys (X :: Zs) :-
  is_append Xs Ys Zs.

% 4. Conditional rule:
% wp(if B then C1 else C2, Q) = (B ⇒ wp(C1, Q)) ∧ (¬B ⇒ wp(C2, Q))
vcg (c_if B C1 C2) Q (p_and (p_imp BAssert Pre1) (p_imp (p_not BAssert) Pre2)) VCs :-
  b_to_assert B BAssert,
  vcg C1 Q Pre1 VCs1,
  vcg C2 Q Pre2 VCs2,
  is_append VCs1 VCs2 VCs.

% 5. While rule with loop invariant Inv:
% Precondition is Inv.
% Generates two verification conditions:
% (a) Inv ∧ B ⇒ wp(C, Inv)  (loop body preserves invariant)
% (b) Inv ∧ ¬B ⇒ Q          (invariant implies postcondition on exit)
vcg (c_while B Inv C) Q Inv (VC1 :: VC2 :: VCsBody) :-
  b_to_assert B BAssert,
  vcg C Inv PreBody VCsBody,
  VC1 = p_imp (p_and Inv BAssert) PreBody,
  VC2 = p_imp (p_and Inv (p_not BAssert)) Q.

% ============================================================================
% Semantic Entailment & VC Discharging
% ============================================================================

% Simple algebraic and propositional proof search to discharge generated VCs
type valid_assert assert -> o.

valid_assert p_true.
valid_assert (p_imp P P).
valid_assert (p_imp p_false _).
valid_assert (p_imp _ p_true).

% P ∧ Q ⇒ P, P ∧ Q ⇒ Q
valid_assert (p_imp (p_and P _) P).
valid_assert (p_imp (p_and _ Q) Q).

% Equality reflexivity: E = E
valid_assert (p_eq E E).

% Arithmetic simplification for constant equalities
valid_assert (p_eq (a_plus (a_num N1) (a_num N2)) (a_num Sum)) :-
  Sum is N1 + N2.
valid_assert (p_eq (a_sub (a_num N1) (a_num N2)) (a_num Diff)) :-
  Diff is N1 - N2.

% Implication deduction:
valid_assert (p_imp P Q) :-
  valid_assert Q.

% Discharge all verification conditions:
type discharge_all list assert -> o.
discharge_all nil.
discharge_all (VC :: Rest) :-
  valid_assert VC,
  discharge_all Rest.

% Verify Hoare triple: {P} C {Q}
% Generates wp Pre and VCs, checks P ⇒ Pre and discharges all VCs.
type hoare_verify assert -> cmd -> assert -> o.
hoare_verify P Cmd Q :-
  vcg Cmd Q Pre VCs,
  valid_assert (p_imp P Pre),
  discharge_all VCs.

% ============================================================================
% Example Queries & Program Verifications
% ============================================================================

% 1. Simple assignment verification:
% {x = 5} x := x + 1 {x = 6}
query succeeds ?
  vcg (c_assign "x" (a_plus (a_var "x") (a_num 1)))
      (p_eq (a_var "x") (a_num 6))
      Pre nil,
  Pre = p_eq (a_plus (a_var "x") (a_num 1)) (a_num 6).

% 2. In-place variable swap verification:
% t := x; x := y; y := t
% Verifies that starting with x = A ∧ y = B, we end with x = B ∧ y = A.
type swap_cmd cmd.
swap_cmd
  (c_seq (c_assign "t" (a_var "x"))
         (c_seq (c_assign "x" (a_var "y"))
                (c_assign "y" (a_var "t")))).

query succeeds ?
  swap_cmd Swap,
  vcg Swap
      (p_and (p_eq (a_var "x") (a_num 20)) (p_eq (a_var "y") (a_num 10)))
      Pre nil,
  Pre = p_and (p_eq (a_var "y") (a_num 20)) (p_eq (a_var "x") (a_num 10)).

% 3. Conditional verification condition generation:
% if x > 0 then y := x else y := 0
query succeeds ?
  vcg (c_if (b_gt (a_var "x") (a_num 0))
            (c_assign "y" (a_var "x"))
            (c_assign "y" (a_num 0)))
      (p_ge (a_var "y") (a_num 0))
      Pre nil.

% 4. While loop VCG (summation / countdown invariant):
% while n > 0 do {s >= 0} (n := n - 1)
query succeeds ?
  vcg (c_while (b_gt (a_var "n") (a_num 0))
               (p_ge (a_var "s") (a_num 0))
               (c_assign "n" (a_sub (a_var "n") (a_num 1))))
      (p_ge (a_var "s") (a_num 0))
      Inv VCs,
  Inv = p_ge (a_var "s") (a_num 0).
