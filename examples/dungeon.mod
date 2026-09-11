% title: Dungeon Adventure
% tags: game, adventure, interactive-fiction, logic, puzzles
% summary: Interactive text-based dungeon adventure. Explore chambers, collect keys,
%   search for hidden treasures using PRNG, unlock the ancient vault, and escape!

module dungeon.

accumulate game_lib.

kind state  type.
kind action type.

% dungeon_state Location Inventory VaultDoorStatus PRNGSeed
type dungeon_state string -> list string -> string -> int -> state.

% --- Actions ---
type go        string -> action.
type take      string -> action.
type unlock    action.
type search    action.
type look      action.

% --- World Map ---
type room_name string -> string -> o.
type room_desc string -> string -> o.
type passage   string -> string -> string -> o.
type room_item string -> string -> o.

room_name "entrance" "Dungeon Entrance".
room_desc "entrance" "Cold wind howls from the iron gates behind you. A dark archway leads north.".

room_name "hall" "Grand Columned Hall".
room_desc "hall" "Towering stone pillars support a vaulted ceiling. Passages lead south, east, and north towards a locked vault door.".

room_name "library" "Forgotten Library".
room_desc "library" "Dusty tomes and shattered scrolls line rotting bookshelves. A heavy bronze_key rests upon a stone reading lectern.".

room_name "vault" "Inner Treasure Sanctuary".
room_desc "vault" "Glowing runes pulse along obsidian walls. At the center pedestal rests the legendary crystal_orb!".

passage "entrance" "north" "hall".
passage "hall" "south" "entrance".
passage "hall" "east" "library".
passage "library" "west" "hall".
passage "hall" "north" "vault".

room_item "library" "bronze_key".
room_item "vault" "crystal_orb".

% --- Game Initialization ---
type game_init      state -> o.
type game_init_seed int -> state -> o.

game_init_seed Seed (dungeon_state "entrance" nil "locked" Seed).

game_init State :-
  game_init_seed 777 State.

% --- Inspection Queries ---
type room_exits  string -> list string -> o.
type list_items  list string -> string -> o.

room_exits "entrance" ("north" :: nil).
room_exits "hall" ("south" :: "east" :: "north" :: nil).
room_exits "library" ("west" :: nil).
room_exits "vault" ("south" :: nil).

list_items nil "none".
list_items (I :: nil) I.
list_items (I1 :: I2 :: Is) Out :-
  list_items (I2 :: Is) Rest,
  P is I1 ^ ", ",
  Out is P ^ Rest.

% --- Game Step ---
type game_step action -> state -> state -> string -> o.

% Action: look
game_step look S S "You examine your surroundings carefully.".

% Action: go Direction
game_step (go "north") (dungeon_state "hall" Inv "locked" Seed) (dungeon_state "hall" Inv "locked" Seed) "The iron vault door to the north is locked with a heavy bronze keyway." :- !.

game_step (go "south") (dungeon_state "vault" Inv Door Seed) (dungeon_state "hall" Inv Door Seed) "You step back south into the grand hall." :- !.

game_step (go Dir) (dungeon_state Loc Inv Door Seed) (dungeon_state NextLoc Inv Door Seed) Msg :-
  passage Loc Dir NextLoc,
  room_name NextLoc Name,
  Msg is "You walk " ^ Dir ^ " into the " ^ Name ^ ".".

% Action: take Item
game_step (take "bronze_key") (dungeon_state "library" Inv Door Seed) (dungeon_state "library" ("bronze_key" :: Inv) Door Seed) "You take the heavy bronze_key." :-
  not (member "bronze_key" Inv), !.

game_step (take "crystal_orb") (dungeon_state "vault" Inv Door Seed) (dungeon_state "vault" ("crystal_orb" :: Inv) Door Seed) "You lift the glowing crystal_orb from the pedestal! The dungeon begins to rumble—escape to the entrance!" :-
  not (member "crystal_orb" Inv), !.

% Action: unlock
game_step unlock (dungeon_state "hall" Inv "locked" Seed) (dungeon_state "hall" Inv "unlocked" Seed) "You insert the bronze_key into the vault lock and turn it with a loud CLICK! The vault door swings open to the north." :-
  member "bronze_key" Inv, !.

game_step unlock (dungeon_state "hall" _ "unlocked" Seed) (dungeon_state "hall" _ "unlocked" Seed) "The vault door is already unlocked." :- !.

% Action: search (uses PRNG to find hidden treasures)
game_step search (dungeon_state Loc Inv Door Seed) (dungeon_state Loc ("ruby_gem" :: Inv) Door NextSeed) "Searching the shadows, you discover a sparkling ruby_gem!" :-
  not (member "ruby_gem" Inv),
  dice_roll Seed 6 NextSeed Roll,
  Roll >= 5, !.

game_step search (dungeon_state Loc Inv Door Seed) (dungeon_state Loc Inv Door NextSeed) "You search the area thoroughly, but find nothing of interest." :-
  dice_roll Seed 6 NextSeed _.

% --- Game Rendering ---
type game_render state -> string -> o.

game_render (dungeon_state Loc Inv Door _) Out :-
  room_name Loc RName,
  room_desc Loc RDesc,
  list_items Inv InvStr,
  H1 is "=== " ^ RName ^ " ===\n",
  H2 is H1 ^ RDesc ^ "\n\n",
  InvLine is "Inventory: [" ^ InvStr ^ "]\n",
  VaultLine is "Vault Door: " ^ Door ^ "\n",
  HelpLine is "\nActions: go \"north\". | take \"item\". | unlock. | search. | look.\n",
  P1 is H2 ^ InvLine,
  P2 is P1 ^ VaultLine,
  Out is P2 ^ HelpLine.

% --- Game Over Condition ---
type game_over state -> string -> o.

game_over (dungeon_state "entrance" Inv _ _) "VICTORY! You escaped the dungeon with the legendary Crystal Orb in hand!" :-
  member "crystal_orb" Inv, !.

% --- Game Help ---
type game_help string -> o.
game_help
  "Commands:\n  go \"north\".         Move in a direction (\"north\", \"south\", \"east\", \"west\")\n  take \"item\".       Pick up an item in the room\n  unlock.            Unlock the door using a key in your inventory\n  search.            Search the room for hidden treasures (PRNG)\n  look.              Re-examine the room\n  :undo              Undo your previous move\n".

% --- Tests ---
query succeeds ? game_init S.
query succeeds ? game_step (go "north") (dungeon_state "entrance" nil "locked" 100) S2 Msg.
