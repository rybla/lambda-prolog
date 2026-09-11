% title: Game Library
% tags: games, library, prng, ascii, rendering, grid
% summary: Standard library for building text-based games in lambda-Prolog:
%   PRNG operations, string conversions, 2D matrix utilities, and ASCII board renderers.

module game_lib.

accumulate lists.
accumulate strings.

% --- Pseudo-Random Number Generation (PRNG) ---
type prng_step   int -> int -> int -> o.
type prng_range  int -> int -> int -> int -> int -> o.
type dice_roll   int -> int -> int -> int -> o.

prng_step S S' Val :-
  S' is prng_next_seed S,
  Val is prng_next_val S.

prng_range S Low High S' Val :-
  S' is prng_next_seed S,
  Val is prng_range_val S Low High.

dice_roll S Sides S' Val :-
  prng_range S 1 Sides S' Val.

% --- String & Line Formatting ---
type int_string   int -> string -> o.
type str_length   string -> int -> o.
type concat_lines list string -> string -> o.

int_string N S :- S is to_string N.

str_length S L :- L is string_length S.

concat_lines nil "".
concat_lines (L :: nil) L.
concat_lines (L1 :: L2 :: Rest) Out :-
  concat_lines (L2 :: Rest) RestOut,
  LineWithNl is L1 ^ "\n",
  Out is LineWithNl ^ RestOut.

% --- 2D Grid / Matrix Accessors ---
type replace_nth1  int -> list A -> A -> list A -> o.
type get_cell      int -> int -> list (list A) -> A -> o.
type set_cell      int -> int -> A -> list (list A) -> list (list A) -> o.

replace_nth1 1 (_ :: Xs) NewVal (NewVal :: Xs).
replace_nth1 N (X :: Xs) NewVal (X :: Ys) :-
  N > 1, M is N - 1, replace_nth1 M Xs NewVal Ys.

get_cell Row Col Board Val :-
  nth1 Row Board RowList,
  nth1 Col RowList Val.

set_cell Row Col Val Board NewBoard :-
  nth1 Row Board RowList,
  replace_nth1 Col RowList Val NewRowList,
  replace_nth1 Row Board NewRowList NewBoard.

% --- ASCII 3x3 Grid Renderer ---
type render_row3   string -> string -> string -> string -> o.
type render_board3 list (list string) -> string -> o.

render_row3 C1 C2 C3 Out :-
  P1 is "| " ^ C1 ^ " | ",
  P2 is P1 ^ C2 ^ " | ",
  Out is P2 ^ C3 ^ " |".

render_board3 ((R11 :: R12 :: R13 :: nil) :: (R21 :: R22 :: R23 :: nil) :: (R31 :: R32 :: R33 :: nil) :: nil) Out :-
  Div is "+---+---+---+\n",
  render_row3 R11 R12 R13 Row1,
  render_row3 R21 R22 R23 Row2,
  render_row3 R31 R32 R33 Row3,
  L1 is Div ^ Row1 ^ "\n",
  L2 is L1 ^ Div ^ Row2 ^ "\n",
  L3 is L2 ^ Div ^ Row3 ^ "\n",
  Out is L3 ^ Div.

% --- Example Queries ---
query succeeds ? prng_step 100 S V.
query succeeds ? prng_range 100 1 6 S V.
query succeeds ? dice_roll 100 20 S V.
query succeeds ? int_string 42 S.
query succeeds ? str_length "lambda" 6.
query succeeds ? get_cell 2 2 ((1 :: 2 :: 3 :: nil) :: (4 :: 5 :: 6 :: nil) :: (7 :: 8 :: 9 :: nil) :: nil) 5.
query succeeds ? set_cell 1 1 "X" (("." :: "." :: "." :: nil) :: ("." :: "." :: "." :: nil) :: ("." :: "." :: "." :: nil) :: nil) B.
query succeeds ? render_board3 (("X" :: "O" :: "X" :: nil) :: ("." :: "X" :: "." :: nil) :: ("O" :: "." :: "O" :: nil) :: nil) Out.
