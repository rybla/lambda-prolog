% title: Definite Clause Grammars (DCG)
% tags: dcg, grammar, parsing, difference-lists, nlp
% summary: Definite Clause Grammars implemented using difference lists,
%   showcasing natural language parsing with subject-verb number agreement,
%   and an arithmetic expression parser building ASTs with operator precedence.

module dcg.

% --- Part 1: Natural Language Grammar with Agreement Features ---
kind num type.
type sg, pl num.

% Terminals and non-terminals for syntax
type sentence     list string -> list string -> o.
type noun_phrase  num -> list string -> list string -> o.
type verb_phrase  num -> list string -> list string -> o.
type determiner   num -> list string -> list string -> o.
type noun         num -> list string -> list string -> o.
type verb         num -> list string -> list string -> o.
type trans_verb   num -> list string -> list string -> o.

% Sentence = NP(N) + VP(N) ensuring agreement in number N
sentence S0 S :-
  noun_phrase N S0 S1,
  verb_phrase N S1 S.

% Noun phrase = Det(N) + Noun(N)
noun_phrase N S0 S :-
  determiner N S0 S1,
  noun N S1 S.

% Intransitive verb phrase
verb_phrase N S0 S :-
  verb N S0 S.

% Transitive verb phrase = TV(N) + NP(_)
verb_phrase N S0 S :-
  trans_verb N S0 S1,
  noun_phrase _ S1 S.

% Lexicon
determiner _  ("the" :: S) S.
determiner sg ("a" :: S) S.
determiner pl ("some" :: S) S.

noun sg ("cat" :: S) S.
noun pl ("cats" :: S) S.
noun sg ("dog" :: S) S.
noun pl ("dogs" :: S) S.
noun sg ("mouse" :: S) S.
noun pl ("mice" :: S) S.

verb sg ("sleeps" :: S) S.
verb pl ("sleep" :: S) S.

trans_verb sg ("chases" :: S) S.
trans_verb pl ("chase" :: S) S.

% Helper to parse a complete sentence from a list
type parse_sentence list string -> o.
parse_sentence Words :-
  sentence Words nil.

% --- Part 2: Arithmetic Expression Parser with Operator Precedence ---
kind asexp type.
type num_ast int -> asexp.
type add_ast asexp -> asexp -> asexp.
type mul_ast asexp -> asexp -> asexp.

type expr_p   asexp -> list string -> list string -> o.
type term_p   asexp -> list string -> list string -> o.
type factor_p asexp -> list string -> list string -> o.
type eval_ast asexp -> int -> o.

% expr ::= term ( "+" expr | epsilon )
expr_p (add_ast T E) S0 S :-
  term_p T S0 ("+" :: S1),
  expr_p E S1 S.
expr_p T S0 S :-
  term_p T S0 S.

% term ::= factor ( "*" term | epsilon )
term_p (mul_ast F T) S0 S :-
  factor_p F S0 ("*" :: S1),
  term_p T S1 S.
term_p F S0 S :-
  factor_p F S0 S.

% factor ::= "(" expr ")" | number
factor_p E ("(" :: S0) S :-
  expr_p E S0 (")" :: S).
factor_p (num_ast 0) ("0" :: S) S.
factor_p (num_ast 1) ("1" :: S) S.
factor_p (num_ast 2) ("2" :: S) S.
factor_p (num_ast 3) ("3" :: S) S.
factor_p (num_ast 4) ("4" :: S) S.
factor_p (num_ast 5) ("5" :: S) S.

% Evaluator on parsed AST
eval_ast (num_ast N) N.
eval_ast (add_ast E1 E2) V :-
  eval_ast E1 V1,
  eval_ast E2 V2,
  V is V1 + V2.
eval_ast (mul_ast E1 E2) V :-
  eval_ast E1 V1,
  eval_ast E2 V2,
  V is V1 * V2.

type parse_and_eval list string -> int -> o.
parse_and_eval Tokens Result :-
  expr_p Ast Tokens nil,
  eval_ast Ast Result.

% ---------------------------------------------------------------------------
% Example queries:
%   ?- parse_sentence ("the" :: "cat" :: "sleeps" :: nil).
%      yes
%   ?- parse_sentence ("the" :: "cats" :: "sleeps" :: nil).
%      no (agreement failure)
%   ?- expr_p Ast ("2" :: "+" :: "3" :: "*" :: "4" :: nil) nil.
%   ?- parse_and_eval ("2" :: "+" :: "3" :: "*" :: "4" :: nil) Res.
%      Res = 14
