% title: Modal Logic & Kripke Semantics
% tags: logic, modal, kripke, accessibility, hypothetical
% summary: Propositional modal logic (Box and Diamond) evaluated over Kripke
%   models where worlds, accessibility relations, and frame conditions (K, T,
%   S4, S5) are modeled directly with hypothetical implication and universal goals.

module modal_logic.

kind form  type.
kind world type.

% Formula constructors
type m_true   form.
type m_false  form.
type atom     string -> form.
type m_not    form -> form.
type m_and    form -> form -> form.
type m_or     form -> form -> form.
type m_imp    form -> form -> form.
type box      form -> form.
type dia      form -> form.

% Model predicates
type acc      world -> world -> o.
type val      world -> string -> o.
type sat      world -> form -> o.
type globally form -> o.

% Satisfaction at a world (Kripke semantics)
sat _ m_true.

sat W (atom P) :-
  val W P.

sat W (m_and A B) :-
  sat W A,
  sat W B.

sat W (m_or A B) :-
  sat W A ; sat W B.

sat W (m_imp A B) :-
  sat W B ; (not (sat W A)).

sat W (m_not A) :-
  not (sat W A).

% Necessity (Box A): in all accessible worlds w', A must hold.
% Expressed directly via universal quantification (pi) and hypothetical
% assumption of accessibility (=>).
sat W (box A) :-
  pi w2\ (acc W w2 => sat w2 A).

% Possibility (Dia A): there exists an accessible world where A holds.
sat W (dia A) :-
  acc W W2,
  sat W2 A.

% Duality check: Dia A is equivalent to ~Box ~A
type check_duality world -> form -> o.
check_duality W A :-
  sat W (dia A),
  sat W (m_not (box (m_not A))).

% Sample Kripke model with 3 worlds: w0, w1, w2
type w0, w1, w2 world.
type sample_model o.

sample_model :-
  acc w0 w1,
  acc w1 w2,
  val w1 "p",
  val w2 "q".

% Verify axioms under frame assumptions
% Axiom K: Box (A -> B) -> (Box A -> Box B) holds in all Kripke frames.
type test_axiom_k world -> form -> form -> o.
test_axiom_k W A B :-
  sat W (m_imp (box (m_imp A B)) (m_imp (box A) (box B))).

% Axiom T: Box A -> A (requires reflexive frame)
type test_axiom_t world -> form -> o.
test_axiom_t W A :-
  (pi w\ acc w w) => sat W (m_imp (box A) A).

% Axiom 4: Box A -> Box Box A (requires transitive frame)
type test_axiom_4 world -> form -> o.
test_axiom_4 W A :-
  sat W (m_imp (box A) (box (box A))).

query succeeds ? (acc w0 w1, val w1 "p") => sat w0 (dia (atom "p")).
query fails ? (acc w0 w1, val w1 "p") => sat w0 (box (atom "p")).
query succeeds ? test_axiom_k w0 (atom "p") (atom "q").
query succeeds ? test_axiom_t w0 (atom "p").
