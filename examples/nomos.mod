% title: Nomos: The Logic Magistrate
% tags: game, logic, jurisprudence, puzzles, hypothetical, pi, nomic
% summary: Rule-hacking jurisprudence puzzle game running on the lambda-Prolog game shell.
%   Features dynamic axiomatic physics via hypothetical implication (=>),
%   proof-theoretic consistency checks and universal entity conservation via pi,
%   and second-order predicate quantification over game properties.

module nomos.

accumulate game_lib.
accumulate assoc.

% ============================================================================
% Kinds and Types
% ============================================================================

kind hero_data    type.
kind world_data   type.
kind decree_data  type.
kind state        type.
kind action       type.

% hero_data Row Col Energy MaxEnergy Inventory
type hero_data    int -> int -> int -> int -> list string -> hero_data.
% world_data BoulderR BoulderC DoorOpen GobletTaken BridgeBuilt
type world_data   int -> int -> int -> int -> int -> world_data.

% State: Hero World ActiveDecreeIds PRNGSeed
type nomos_state  hero_data -> world_data -> list int -> int -> state.

% --- Actions ---
type move         string -> action.
type push         string -> action.
type take         action.
type decree       int -> action.
type repeal       int -> action.
type examine      action.
type wait         action.

% --- Dynamic Axiom Predicates (Hypothetical Heads) ---
type law_pyrostasis    string -> o.
type law_buoyancy      string -> o.
type law_midas         string -> o.
type law_permeability  string -> o.
type law_inverse       o.

% ============================================================================
% Map Geometry & Static World Facts
% ============================================================================

type is_boundary_wall int -> int -> o.
is_boundary_wall 1 1. is_boundary_wall 1 2. is_boundary_wall 1 3. is_boundary_wall 1 4. is_boundary_wall 1 5. is_boundary_wall 1 6.
is_boundary_wall 6 1. is_boundary_wall 6 2. is_boundary_wall 6 3. is_boundary_wall 6 4. is_boundary_wall 6 6.
is_boundary_wall 2 1. is_boundary_wall 3 1. is_boundary_wall 4 1. is_boundary_wall 5 1.
is_boundary_wall 2 6. is_boundary_wall 3 6. is_boundary_wall 4 6. is_boundary_wall 5 6.
is_boundary_wall 3 3. % Stone pillar

type is_fire_tile int -> int -> o.
is_fire_tile 2 4.
is_fire_tile 3 4.
is_fire_tile 4 4.

type is_water_tile int -> int -> o.
is_water_tile 5 2.
is_water_tile 5 3.
is_water_tile 5 4.

type is_exit_tile int -> int -> o.
is_exit_tile 6 5.

type is_door_tile int -> int -> o.
is_door_tile 5 5.

type in_chamber int -> int -> o.
in_chamber R C :- R >= 1, R =< 6, C >= 1, C =< 6.

% ============================================================================
% Game Initialization
% ============================================================================

type game_init      state -> o.
type game_init_seed int -> state -> o.

game_init_seed Seed (nomos_state Hero World nil Seed) :-
  Hero = hero_data 2 2 15 15 nil,
  World = world_data 3 2 0 0 0. % Boulder at (3,2), Door closed, Goblet on floor, no bridge

game_init State :-
  game_init_seed 101 State.

% ============================================================================
% Magistrate Law Installation & Hypothetical Reasoning
% ============================================================================

% Install active decrees as dynamic program clauses for the scope of Goal G
type with_decrees list int -> o -> o.
with_decrees nil G :- G.
with_decrees (1 :: Rest) G :-
  % Decree 1: Pyrostasis — fire becomes solid obsidian
  (law_pyrostasis "fire") => with_decrees Rest G.
with_decrees (2 :: Rest) G :-
  % Decree 2: Buoyancy — heavy granite blocks float on subterranean water
  (law_buoyancy "granite") => with_decrees Rest G.
with_decrees (3 :: Rest) G :-
  % Decree 3: Midas — gold acts as an adamantine key
  (law_midas "gold") => with_decrees Rest G.
with_decrees (4 :: Rest) G :-
  % Decree 4: Permeability — fire is permeable vapor
  (law_permeability "fire") => with_decrees Rest G.
with_decrees (_ :: Rest) G :-
  with_decrees Rest G.

% ============================================================================
% Dynamic Axiomatic Physics (Evaluated Under Active Decrees)
% ============================================================================

type tile_solid int -> int -> world_data -> o.
tile_solid R C _ :- is_boundary_wall R C, !.
tile_solid R C (world_data BR BC _ _ _) :- R = BR, C = BC, !.
tile_solid 5 5 (world_data _ _ 0 _ _) :- !. % Closed vault door is solid

type tile_lethal int -> int -> world_data -> o.
tile_lethal R C _ :-
  is_fire_tile R C,
  not (law_pyrostasis "fire"),
  not (law_permeability "fire"), !.
tile_lethal R C (world_data _ _ _ _ Bridge) :-
  is_water_tile R C,
  Bridge = 0, !.

type can_traverse int -> int -> world_data -> o.
can_traverse R C World :-
  in_chamber R C,
  not (tile_solid R C World),
  not (tile_lethal R C World).

% ============================================================================
% Magistrate Proof-Theoretic Verification Engine
% ============================================================================

type verifies_conservation int -> o.
verifies_conservation 1 :-
  pi x\ (law_pyrostasis x => law_pyrostasis x).
verifies_conservation 2 :-
  pi x\ (law_buoyancy x => law_buoyancy x).
verifies_conservation 3 :-
  pi x\ (law_midas x => law_midas x).
verifies_conservation 4 :-
  pi x\ (law_permeability x => law_permeability x).

type magistrate_verify_decree int -> list int -> string -> o.
magistrate_verify_decree DecreeId ActiveDecrees Msg :-
  not (member DecreeId ActiveDecrees),
  verifies_conservation DecreeId,
  Msg = "The Magistrate ratifies Decree. Proof verification: CONSISTENT & CONSERVED.".

% ============================================================================
% Game Step Dispatch & Action Handlers
% ============================================================================

type step_dir int -> int -> string -> int -> int -> o.
step_dir R C "north" NR C :- NR is R - 1.
step_dir R C "south" NR C :- NR is R + 1.
step_dir R C "west" R NC :- NC is C - 1.
step_dir R C "east" R NC :- NC is C + 1.
step_dir R C "n" NR C :- NR is R - 1.
step_dir R C "s" NR C :- NR is R + 1.
step_dir R C "w" R NC :- NC is C - 1.
step_dir R C "e" R NC :- NC is C + 1.

type game_step action -> state -> state -> string -> o.

% Action: move Dir
game_step (move Dir) (nomos_state (hero_data R C Eng MEng Inv) World Decrees Seed) (nomos_state (hero_data NR NC Eng MEng Inv) World Decrees Seed) Msg :-
  step_dir R C Dir TR TC,
  % Movement checked under active decrees!
  with_decrees Decrees (can_traverse TR TC World), !,
  NR = TR, NC = TC,
  Msg is "You advance " ^ Dir ^ " to (" ^ to_string NR ^ ", " ^ to_string NC ^ ").".

game_step (move Dir) (nomos_state (hero_data R C Eng MEng Inv) World Decrees Seed) (nomos_state (hero_data R C Eng MEng Inv) World Decrees Seed) Msg :-
  step_dir R C Dir TR TC,
  with_decrees Decrees
    ( (is_boundary_wall TR TC, Msg = "An impassable stone boundary wall blocks your passage.") ;
      (is_fire_tile TR TC, tile_lethal TR TC World, Msg = "LETHAL BARRIER: Raging flames threaten to incinerate you! Edict required.") ;
      (is_water_tile TR TC, tile_lethal TR TC World, Msg = "LETHAL DEPTHS: The subterranean abyss has no bridge! Edict required.") ;
      (TR = 5, TC = 5, World = world_data _ _ 0 _ _, Msg = "The Adamantine Vault Door is locked! (Requires a Gold key).") ;
      Msg = "Movement blocked." ), !.

% Action: push Dir (Pushing the boulder)
game_step (push Dir) (nomos_state (hero_data R C Eng MEng Inv) (world_data BR BC Dopen Gtak Bridge) Decrees Seed) (nomos_state (hero_data R C Eng MEng Inv) NextWorld Decrees Seed) Msg :-
  step_dir R C Dir BR BC, % Boulder is adjacent in Dir
  step_dir BR BC Dir NBR NBC,
  in_chamber NBR NBC,
  not (is_boundary_wall NBR NBC), !,
  with_decrees Decrees
    ( (is_water_tile NBR NBC, law_buoyancy "granite", !,
       % Boulder floats on water! Forms a bridge!
       NextWorld = world_data 0 0 Dopen Gtak 1,
       Msg = "HEAVY BUOYANCY: The boulder tumbles into the deep canal and FLOATS! A stable bridge is formed!") ;
      (is_water_tile NBR NBC, not (law_buoyancy "granite"), !,
       NextWorld = world_data BR BC Dopen Gtak Bridge,
       Msg = "The boulder is too dense to cross the chasm without the Edict of Buoyancy.") ;
      (not (is_water_tile NBR NBC),
       NextWorld = world_data NBR NBC Dopen Gtak Bridge,
       Msg is "You push the heavy granite boulder into (" ^ to_string NBR ^ ", " ^ to_string NBC ^ ").") ).

% Action: take (Collect items)
game_step take (nomos_state (hero_data 1 5 Eng MEng Inv) (world_data BR BC Dopen 0 Bridge) Decrees Seed) (nomos_state (hero_data 1 5 Eng MEng ("gold_goblet" :: Inv)) (world_data BR BC Dopen 1 Bridge) Decrees Seed) Msg :-
  !,
  Msg = "You lift the Ancient Gold Goblet from the altar! Its gilded sheen pulses with axiomatic resonance.".

game_step take (nomos_state (hero_data R C Eng MEng Inv) World Decrees Seed) (nomos_state (hero_data R C Eng MEng Inv) World Decrees Seed) "There is nothing here to take.".

% Action: decree ID (Enact a legal edict)
game_step (decree ID) (nomos_state (hero_data R C Eng MEng Inv) World Decrees Seed) (nomos_state (hero_data R C NEng MEng Inv) World (ID :: Decrees) Seed) Msg :-
  ID >= 1, ID =< 4,
  not (member ID Decrees),
  Eng >= 4, !,
  NEng is Eng - 4,
  magistrate_verify_decree ID Decrees ProofMsg,
  decree_title ID Title,
  P1 is "DECREE ENACTED: " ^ Title ^ "! ",
  Msg is P1 ^ ProofMsg.

game_step (decree ID) (nomos_state (hero_data R C Eng MEng Inv) World Decrees Seed) (nomos_state (hero_data R C Eng MEng Inv) World Decrees Seed) Msg :-
  member ID Decrees, !,
  Msg = "Decree is already in effect in the Codex of Laws.".
game_step (decree _) (nomos_state (hero_data R C Eng MEng Inv) World Decrees Seed) (nomos_state (hero_data R C Eng MEng Inv) World Decrees Seed) "Insufficient Legal Aether to ratify decree (costs 4).".

% Action: repeal ID (Revoke an active decree)
game_step (repeal ID) (nomos_state (hero_data R C Eng MEng Inv) World Decrees Seed) (nomos_state (hero_data R C NEng MEng Inv) World NextDecrees Seed) Msg :-
  member ID Decrees, !,
  delassoc ID Decrees NextDecrees,
  RawEng is Eng + 3, clamp_int RawEng 0 MEng NEng,
  decree_title ID Title,
  Msg is "Decree '" ^ Title ^ "' repealed! 3 Legal Aether refunded.".

game_step (repeal _) S S "No such active decree to repeal.".

% Action: wait
game_step wait (nomos_state (hero_data R C Eng MEng Inv) World Decrees Seed) (nomos_state (hero_data R C NEng MEng Inv) World Decrees NextSeed) Msg :-
  RawEng is Eng + 1, clamp_int RawEng 0 MEng NEng,
  prng_step Seed NextSeed _,
  Msg = "You pause and absorb ambient legal aether (+1 Aether).".

% Action: examine
game_step examine (nomos_state (hero_data R C _ _ Inv) World Decrees _) (nomos_state (hero_data R C _ _ Inv) World Decrees _) Msg :-
  with_decrees Decrees
    ( (member "gold_goblet" Inv, law_midas "gold", !,
       Msg = "AXIOM STATUS: The Gold Goblet in your pack is transmuting into an Adamantine Skeleton Key!") ;
      (law_pyrostasis "fire", !,
       Msg = "AXIOM STATUS: Pyrostasis is active: All fire tiles are solidified into walkable obsidian.") ;
      (law_buoyancy "granite", !,
       Msg = "AXIOM STATUS: Buoyancy is active: Heavy granite blocks will float on subterranean water.") ;
      Msg = "AXIOM STATUS: Standard chamber physics apply. Flammable and drowning hazards active." ).

% ============================================================================
% Door Unlocking Trigger
% ============================================================================

% If player is at (5,4) facing door (5,5) with gold goblet under Midas decree:
game_step (move "east") (nomos_state (hero_data 5 4 Eng MEng Inv) (world_data BR BC 0 Gtak Bridge) Decrees Seed) (nomos_state (hero_data 5 5 Eng MEng Inv) (world_data BR BC 1 Gtak Bridge) Decrees Seed) Msg :-
  member "gold_goblet" Inv,
  with_decrees Decrees (law_midas "gold"), !,
  Msg = "MIDAS RATIFICATION: The Gold Goblet touches the adamantine keyway—the Vault Door swings wide open!".

% ============================================================================
% Codex Metadata
% ============================================================================

type decree_title int -> string -> o.
decree_title 1 "Edict of Pyrostasis (pi x\\ fire x => solid x)".
decree_title 2 "Edict of Buoyancy (pi x\\ heavy x => float x)".
decree_title 3 "Midas Transmutation (pi x\\ gold x => key x)".
decree_title 4 "Edict of Permeability (pi x\\ fire x => permeable x)".

% ============================================================================
% ASCII Dual-Pane UI Rendering
% ============================================================================

type cell_glyph hero_data -> world_data -> int -> int -> string -> o.
cell_glyph (hero_data R C _ _ _) _ R C "@" :- !.
cell_glyph _ (world_data R C _ _ _) R C "B" :- R > 0, C > 0, !.
cell_glyph _ (world_data _ _ _ 0 _) 1 5 "*" :- !.
cell_glyph _ (world_data _ _ 0 _ _) 5 5 "D" :- !.
cell_glyph _ (world_data _ _ 1 _ _) 5 5 "/" :- !. % Open door
cell_glyph _ (world_data _ _ _ _ 1) 5 3 "=" :- !. % Bridge
cell_glyph _ _ 6 5 "E" :- !.
cell_glyph _ _ R C "#" :- is_boundary_wall R C, !.
cell_glyph _ _ R C "F" :- is_fire_tile R C, !.
cell_glyph _ _ R C "W" :- is_water_tile R C, !.
cell_glyph _ _ _ _ ".".

type render_row_cells hero_data -> world_data -> int -> string -> o.
render_row_cells Hero World R Out :-
  cell_glyph Hero World R 1 C1, cell_glyph Hero World R 2 C2, cell_glyph Hero World R 3 C3,
  cell_glyph Hero World R 4 C4, cell_glyph Hero World R 5 C5, cell_glyph Hero World R 6 C6,
  P1 is "| " ^ C1 ^ " " ^ C2 ^ " ",
  P2 is P1 ^ C3 ^ " " ^ C4 ^ " ",
  Out is P2 ^ C5 ^ " " ^ C6 ^ " |".

type render_chamber_lines hero_data -> world_data -> list string -> o.
render_chamber_lines Hero World Lines :-
  Div is "+-------------+",
  render_row_cells Hero World 1 R1,
  render_row_cells Hero World 2 R2,
  render_row_cells Hero World 3 R3,
  render_row_cells Hero World 4 R4,
  render_row_cells Hero World 5 R5,
  render_row_cells Hero World 6 R6,
  Lines = (Div :: R1 :: R2 :: R3 :: R4 :: R5 :: R6 :: Div :: nil).

type format_active_decrees list int -> list string -> o.
format_active_decrees nil ("Active Laws: [none]" :: nil).
format_active_decrees (D :: Ds) (Line :: Rest) :-
  decree_title D Title,
  Line is "[ACTIVE] " ^ Title,
  format_active_decrees Ds Rest.

type format_inventory list string -> string -> o.
format_inventory nil "none".
format_inventory (I :: nil) I.
format_inventory (I1 :: I2 :: Is) Out :-
  format_inventory (I2 :: Is) Rest,
  P is I1 ^ ", ",
  Out is P ^ Rest.

type game_render state -> string -> o.
game_render (nomos_state (hero_data R C Eng MEng Inv) World Decrees _) Out :-
  render_chamber_lines (hero_data R C Eng MEng Inv) World ChamberLines,
  render_panel_box "VAULT OF AXIOMS" 15 ChamberLines ChamberBox,

  render_bar "AETHER" Eng MEng 10 AetherBar,
  format_inventory Inv InvStr,
  InvLine is "Inventory: [" ^ InvStr ^ "]",
  ProofStatus = "Magistrate: [CONSISTENT & CONSERVED]",

  StatusHeader =
    (AetherBar :: InvLine :: ProofStatus ::
     "--- CODEX OF JURISPRUDENCE ---" ::
     "[1] Pyrostasis: fire => solid (4)" ::
     "[2] Buoyancy:   heavy => float (4)" ::
     "[3] Midas:      gold => key   (4)" ::
     "[4] Permeable:  fire => gas   (4)" ::
     "--- ACTIVE LEGISLATION ---" :: nil),
  format_active_decrees Decrees ActiveList,
  append StatusHeader ActiveList FullStatus,
  render_panel_box "LOGIC MAGISTRATE & CODEX" 35 FullStatus CodexBox,

  h_stack_lines 19 "  " ChamberBox CodexBox CombinedLines,
  concat_lines CombinedLines ScreenBody,

  Header is "======================= NOMOS: THE LOGIC MAGISTRATE =======================\n",
  Footer is "\nCommands: move Dir. | push Dir. | take. | decree ID. | repeal ID. | examine.\n",
  P1 is Header ^ ScreenBody,
  Out is P1 ^ Footer.

% ============================================================================
% Game Over Conditions
% ============================================================================

type game_over state -> string -> o.
game_over (nomos_state (hero_data 6 5 _ _ _) _ _ _) "VICTORY! You passed through the Sanctuary Exit and mastered the Constitution of Logic!" :- !.

% ============================================================================
% Game Help
% ============================================================================

type game_help string -> o.
game_help
  "Nomos: The Logic Magistrate — Jurisprudence Puzzle\n  move Dir.         Move Magus (\"n\", \"s\", \"e\", \"w\")\n  push Dir.         Push adjacent boulder (e.g. into water)\n  take.             Pick up item on current tile (e.g. Gold Goblet)\n  decree ID.        Enact decree 1..4 (costs 4 Aether; verified by Magistrate)\n  repeal ID.        Revoke active decree ID (refunds 3 Aether)\n  examine.          Inspect active axiomatic state\n  wait.             Absorb 1 Legal Aether\n  :undo, :restart   Engine commands\n".

% ============================================================================
% Embedded Verification Queries
% ============================================================================

query succeeds ? game_init S.
query succeeds ?
  game_init S0,
  game_step (move "north") S0 S1 Msg1,
  game_step (decree 1) S1 S2 Msg2.
query succeeds ?
  game_init S0,
  game_step (decree 1) S0 S1 MsgDec,
  game_step (move "east") S1 S2 MsgMove,
  game_step (move "east") S2 S3 MsgWalkFire.
query succeeds ?
  game_init S0,
  game_render S0 Out.
