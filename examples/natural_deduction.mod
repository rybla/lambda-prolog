% title: Natural Deduction & Curry-Howard Proof Terms
% tags: logic, natural-deduction, curry-howard, proof-terms, intuitionistic
% summary: Intuitionistic propositional natural deduction where proof terms
%   are verified via Curry-Howard isomorphism, using hypothetical reasoning
%   to introduce assumptions and eigenvariables for local hypothesis scoping.

module natural_deduction.

kind prop  type.
kind proof type.

% Proposition constructors
type p_true  prop.
type p_false prop.
type p_atom  string -> prop.
type p_and   prop -> prop -> prop.
type p_or    prop -> prop -> prop.
type p_imp   prop -> prop -> prop.

% Proof term constructors
type tt_p    proof.
type pair_p  proof -> proof -> proof.
type fst_p   proof -> proof.
type snd_p   proof -> proof.
type inl_p   prop -> proof -> proof.
type inr_p   prop -> proof -> proof.
type case_p  proof -> (proof -> proof) -> (proof -> proof) -> proof.
type lam_p   prop -> (proof -> proof) -> proof.
type app_p   proof -> proof -> proof.
type abort_p prop -> proof -> proof.

% Proof checking predicate: has_proof Term Proposition
type has_proof proof -> prop -> o.
type proves    prop -> proof -> o.

% True introduction: ⊢ tt : ⊤
has_proof tt_p p_true.

% Conjunction introduction: ⊢ pair P Q : A ∧ B
has_proof (pair_p P Q) (p_and A B) :-
  has_proof P A,
  has_proof Q B.

% Conjunction elimination
has_proof (fst_p P) A :-
  has_proof P (p_and A _).

has_proof (snd_p P) B :-
  has_proof P (p_and _ B).

% Disjunction introduction
has_proof (inl_p B P) (p_or A B) :-
  has_proof P A.

has_proof (inr_p A P) (p_or A B) :-
  has_proof P B.

% Disjunction elimination (proof by cases)
has_proof (case_p P L R) C :-
  has_proof P (p_or A B),
  (pi x\ has_proof x A => has_proof (L x) C),
  (pi y\ has_proof y B => has_proof (R y) C).

% Implication introduction (hypothetical deduction)
has_proof (lam_p A Body) (p_imp A B) :-
  pi x\ (has_proof x A => has_proof (Body x) B).

% Implication elimination (Modus Ponens)
has_proof (app_p F Arg) B :-
  has_proof F (p_imp A B),
  has_proof Arg A.

% Falsehood elimination (ex falso quodlibet)
has_proof (abort_p C P) C :-
  has_proof P p_false.

% Automated proof synthesis for tautologies
proves Prop Proof :-
  has_proof Proof Prop.

% ---------------------------------------------------------------------------
% Example queries:
%   ?- % Identity: A -> A
%      proves (p_imp (p_atom "A") (p_atom "A")) Proof.
%      Proof = lam_p (p_atom "A") (x\ x)
%
%   ?- % And commutativity: A and B -> B and A
%      has_proof (lam_p (p_and (p_atom "a") (p_atom "b"))
%                   (p\ pair_p (snd_p p) (fst_p p)))
%                (p_imp (p_and (p_atom "a") (p_atom "b"))
%                       (p_and (p_atom "b") (p_atom "a"))).
%      yes
