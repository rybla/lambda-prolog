% title: Tic-Tac-Toe Game
% tags: game, logic, board, adversarial, interactive
% summary: Interactive Tic-Tac-Toe game running on the lambda-Prolog game shell.
%   Features 2D ASCII grid rendering, turn alternation, rule checking, and automated AI opponent.

module tictactoe.

accumulate game_lib.

kind state  type.
kind action type.

type game_state   list (list string) -> string -> int -> state.
type play         int -> int -> action.

type initial_board list (list string) -> o.
initial_board
  (("." :: "." :: "." :: nil) ::
   ("." :: "." :: "." :: nil) ::
   ("." :: "." :: "." :: nil) :: nil).

% --- Game Initialization ---
type game_init      state -> o.
type game_init_seed int -> state -> o.

game_init_seed Seed (game_state B "X" Seed) :-
  initial_board B.

game_init State :-
  game_init_seed 42 State.

% --- Win Condition & Board Checking ---
type win_line   string -> list (list string) -> o.
type board_full list (list string) -> o.
type cell_empty int -> int -> list (list string) -> o.
type open_cells list (list string) -> list (pr int int) -> o.

cell_empty R C B :-
  get_cell R C B ".".

win_line P B :- get_cell 1 1 B P, get_cell 1 2 B P, get_cell 1 3 B P.
win_line P B :- get_cell 2 1 B P, get_cell 2 2 B P, get_cell 2 3 B P.
win_line P B :- get_cell 3 1 B P, get_cell 3 2 B P, get_cell 3 3 B P.
win_line P B :- get_cell 1 1 B P, get_cell 2 1 B P, get_cell 3 1 B P.
win_line P B :- get_cell 1 2 B P, get_cell 2 2 B P, get_cell 3 2 B P.
win_line P B :- get_cell 1 3 B P, get_cell 2 3 B P, get_cell 3 3 B P.
win_line P B :- get_cell 1 1 B P, get_cell 2 2 B P, get_cell 3 3 B P.
win_line P B :- get_cell 1 3 B P, get_cell 2 2 B P, get_cell 3 1 B P.

board_full B :-
  not (cell_empty 1 1 B), not (cell_empty 1 2 B), not (cell_empty 1 3 B),
  not (cell_empty 2 1 B), not (cell_empty 2 2 B), not (cell_empty 2 3 B),
  not (cell_empty 3 1 B), not (cell_empty 3 2 B), not (cell_empty 3 3 B).

% --- Inspection Queries ---
type valid_move   int -> int -> o.
type winning_move string -> int -> int -> o.

valid_move R C :-
  (R = 1 ; R = 2 ; R = 3),
  (C = 1 ; C = 2 ; C = 3).

winning_move P R C :-
  valid_move R C.

% --- AI Opponent Strategy ---
type ai_choose_move list (list string) -> int -> int -> int -> int -> o.
type pick_first_open list (list string) -> int -> int -> o.

pick_first_open B 1 1 :- cell_empty 1 1 B, !.
pick_first_open B 1 2 :- cell_empty 1 2 B, !.
pick_first_open B 1 3 :- cell_empty 1 3 B, !.
pick_first_open B 2 1 :- cell_empty 2 1 B, !.
pick_first_open B 2 2 :- cell_empty 2 2 B, !.
pick_first_open B 2 3 :- cell_empty 2 3 B, !.
pick_first_open B 3 1 :- cell_empty 3 1 B, !.
pick_first_open B 3 2 :- cell_empty 3 2 B, !.
pick_first_open B 3 3 :- cell_empty 3 3 B, !.

% AI Strategy: 1) Win if possible, 2) Block player, 3) Pick center, 4) Pick open
ai_choose_move B Seed AR AC NextSeed :-
  valid_move AR AC, cell_empty AR AC B,
  set_cell AR AC "O" B TestB, win_line "O" TestB, !,
  NextSeed is prng_next_seed Seed.
ai_choose_move B Seed AR AC NextSeed :-
  valid_move AR AC, cell_empty AR AC B,
  set_cell AR AC "X" B TestB, win_line "X" TestB, !,
  NextSeed is prng_next_seed Seed.
ai_choose_move B Seed 2 2 NextSeed :-
  cell_empty 2 2 B, !,
  NextSeed is prng_next_seed Seed.
ai_choose_move B Seed AR AC NextSeed :-
  pick_first_open B AR AC,
  NextSeed is prng_next_seed Seed.

% --- Game Step ---
type game_step action -> state -> state -> string -> o.

game_step (play R C) (game_state B "X" Seed) (game_state NextB "X" Seed) Msg :-
  R >= 1, R =< 3,
  C >= 1, C =< 3,
  cell_empty R C B,
  set_cell R C "X" B NextB,
  win_line "X" NextB, !,
  P1 is "Player X played (" ^ to_string R ^ ", " ^ to_string C,
  Msg is P1 ^ ") and won!".

game_step (play R C) (game_state B "X" Seed) (game_state NextB "X" Seed) Msg :-
  R >= 1, R =< 3,
  C >= 1, C =< 3,
  cell_empty R C B,
  set_cell R C "X" B NextB,
  board_full NextB, !,
  P1 is "Player X played (" ^ to_string R ^ ", " ^ to_string C,
  Msg is P1 ^ "). The board is now full!".

game_step (play R C) (game_state B "X" Seed) (game_state NextB "X" NextSeed) Msg :-
  R >= 1, R =< 3,
  C >= 1, C =< 3,
  cell_empty R C B,
  set_cell R C "X" B BAfterPlayer,
  ai_choose_move BAfterPlayer Seed AR AC NextSeed,
  set_cell AR AC "O" BAfterPlayer NextB,
  P1 is "You played (" ^ to_string R ^ ", " ^ to_string C ^ "). ",
  P2 is P1 ^ "AI played (" ^ to_string AR ^ ", ",
  Msg is P2 ^ to_string AC ^ ").".

% --- Game Rendering ---
type game_render state -> string -> o.

game_render (game_state B _ _) Out :-
  render_board3 B BoardTxt,
  Header is "=== TIC-TAC-TOE ===\n",
  Footer is "\nSubmit 'play Row Col.' (1..3). Example: 'play 1 1.'\n",
  Part is Header ^ BoardTxt,
  Out is Part ^ Footer.

% --- Game Over ---
type game_over state -> string -> o.

game_over (game_state B _ _) "VICTORY! You connected 3 in a row!" :-
  win_line "X" B, !.

game_over (game_state B _ _) "DEFEAT! The AI connected 3 in a row!" :-
  win_line "O" B, !.

game_over (game_state B _ _) "DRAW! The board is full with no winner." :-
  board_full B, !.

% --- Game Help ---
type game_help string -> o.
game_help
  "Commands:\n  play Row Col.    Place your mark (Row 1..3, Col 1..3)\n  valid_move R C.  Inspect legal grid positions\n  :undo            Undo your previous move\n  :restart         Restart from empty board\n".

% --- Tests ---
query succeeds ? game_init S.
query succeeds ? initial_board B, game_step (play 2 2) (game_state B "X" 100) S2 Msg.
