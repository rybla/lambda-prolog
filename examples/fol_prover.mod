% title: First-Order Logic Sequent Calculus Prover
% tags: logic, sequent-calculus, first-order, eigenvariables, automated-theorem-proving
% summary: Automated theorem prover for first-order logic using Gentzen's
%   sequent calculus LK/LJ, leveraging meta-level eigenvariables (pi) for universal
%   quantifiers on the right and existential quantifiers on the left.

module fol_prover.

kind ind  type.
kind form type.

% Formula syntax
type f_atom string -> list ind -> form.
type f_not  form -> form.
type f_and  form -> form -> form.
type f_or   form -> form -> form.
type f_imp  form -> form -> form.
type f_all  (ind -> form) -> form.
type f_some (ind -> form) -> form.

% Sequent prover: prove_d Depth Gamma Delta (Gamma ⊢ Delta)
type prove   form -> o.
type seq     int -> list form -> list form -> o.
type memb    form -> list form -> o.

memb X (X :: _).
memb X (_ :: Xs) :- memb X Xs.

prove F :-
  seq 6 nil (F :: nil).

% Axiom: Γ, A ⊢ Δ, A
seq _ Gamma Delta :-
  memb A Gamma,
  memb A Delta, !.

% Left conjunction: Γ, A ∧ B ⊢ Δ
seq D (f_and A B :: Gamma) Delta :-
  D > 0, D1 is D - 1,
  seq D1 (A :: B :: Gamma) Delta.

% Right conjunction: Γ ⊢ A ∧ B, Δ
seq D Gamma (f_and A B :: Delta) :-
  D > 0, D1 is D - 1,
  seq D1 Gamma (A :: Delta),
  seq D1 Gamma (B :: Delta).

% Left disjunction: Γ, A ∨ B ⊢ Δ
seq D (f_or A B :: Gamma) Delta :-
  D > 0, D1 is D - 1,
  seq D1 (A :: Gamma) Delta,
  seq D1 (B :: Gamma) Delta.

% Right disjunction: Γ ⊢ A ∨ B, Δ
seq D Gamma (f_or A B :: Delta) :-
  D > 0, D1 is D - 1,
  seq D1 Gamma (A :: B :: Delta).

% Left implication: Γ, A → B ⊢ Δ
seq D (f_imp A B :: Gamma) Delta :-
  D > 0, D1 is D - 1,
  seq D1 Gamma (A :: Delta),
  seq D1 (B :: Gamma) Delta.

% Right implication: Γ ⊢ A → B, Δ
seq D Gamma (f_imp A B :: Delta) :-
  D > 0, D1 is D - 1,
  seq D1 (A :: Gamma) (B :: Delta).

% Left negation: Γ, ¬A ⊢ Δ
seq D (f_not A :: Gamma) Delta :-
  D > 0, D1 is D - 1,
  seq D1 Gamma (A :: Delta).

% Right negation: Γ ⊢ ¬A, Δ
seq D Gamma (f_not A :: Delta) :-
  D > 0, D1 is D - 1,
  seq D1 (A :: Gamma) Delta.

% Right universal quantifier (∀R): Γ ⊢ ∀x. A(x), Δ
% Soundness requires introducing a fresh eigenvariable c that does not occur in Γ, Δ.
% In λProlog, this is directly provided by the meta-level quantifier `pi c\`.
seq D Gamma (f_all A :: Delta) :-
  D > 0, D1 is D - 1,
  pi c\ seq D1 Gamma (A c :: Delta).

% Left existential quantifier (∃L): Γ, ∃x. A(x) ⊢ Δ
% Also requires a fresh eigenvariable c via `pi c\`.
seq D (f_some A :: Gamma) Delta :-
  D > 0, D1 is D - 1,
  pi c\ seq D1 (A c :: Gamma) Delta.

% Right existential quantifier (∃R): Γ ⊢ ∃x. A(x), Δ
% Replaced with a logic variable T to be instantiated.
seq D Gamma (f_some A :: Delta) :-
  D > 0, D1 is D - 1,
  seq D1 Gamma (A _ :: Delta).

% Left universal quantifier (∀L): Γ, ∀x. A(x) ⊢ Δ
seq D (f_all A :: Gamma) Delta :-
  D > 0, D1 is D - 1,
  seq D1 (A _ :: Gamma) Delta.

% ---------------------------------------------------------------------------
% Example queries
query succeeds ? prove (f_imp (f_all (x\ f_atom "P" (x :: nil))) (f_atom "P" (_ :: nil))).
query succeeds ? prove (f_imp (f_all (x\ f_and (f_atom "P" (x :: nil)) (f_atom "Q" (x :: nil)))) (f_and (f_all (x\ f_atom "P" (x :: nil))) (f_all (x\ f_atom "Q" (x :: nil))))).
