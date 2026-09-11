% title: The Archmage's Grimoire
% tags: game, hoas, higher-order, roguelike, combat, magic, beta
% summary: Tactical spellcrafting roguelike running on the lambda-Prolog game shell.
%   Features higher-order abstract syntax (HOAS) spells, beta-reduction over targets,
%   hypothetical battlefield auras (=>), higher-order pattern matching counterspells,
%   and a modular dual-pane ASCII interface.

module grimoire.

accumulate game_lib.
accumulate assoc.

% ============================================================================
% Kinds and Types
% ============================================================================

kind entity     type.
kind spell      type.
kind hero_rec   type.
kind enemy_rec  type.
kind aura_rec   type.
kind state      type.
kind action     type.

% --- Spell Constructors (HOAS & Combinators) ---
type zap        string -> int -> spell.
type push       string -> string -> spell.
type freeze     string -> int -> spell.
type heal       string -> int -> spell.
type drain      string -> int -> spell.
type chain      spell -> spell -> spell.
type aoe        int -> (string -> spell) -> spell.
type empower    int -> spell -> spell.
type abs        (string -> spell) -> spell.

% --- Hypothetical Aura Predicates ---
type aura_ward_fire      string -> o.
type aura_shield_reflect string -> o.
type aura_amp_magic      string -> o.

% --- Record Constructors ---
% hero_rec HP MaxHP MP MaxMP Row Col CounterPrimed Grimoire
type hero_rec   int -> int -> int -> int -> int -> int -> int -> list (pair int spell) -> hero_rec.
% enemy_rec ID Glyph Name HP MaxHP Row Col FrozenTurns InnateSpell
type enemy_rec  string -> string -> string -> int -> int -> int -> int -> int -> spell -> enemy_rec.
% aura_rec Name RemainingTurns
type aura_rec   string -> int -> aura_rec.

% state: Hero Enemies Auras Seed
type game_state hero_rec -> list enemy_rec -> list aura_rec -> int -> state.

% --- Actions ---
type move         string -> action.
type cast         int -> string -> action.
type cast_aoe     int -> action.
type craft        int -> spell -> action.
type enchant      string -> int -> action.
type counter      action.
type meditate     action.
type inspect      action.

% ============================================================================
% Map and Obstacle Geometry (5x5 Arena)
% ============================================================================

type is_pillar int -> int -> o.
is_pillar 2 2.
is_pillar 4 4.

type in_bounds int -> int -> o.
in_bounds R C :- R >= 1, R =< 5, C >= 1, C =< 5.

type is_blocked int -> int -> list enemy_rec -> o.
is_blocked R C _ :- is_pillar R C, !.
is_blocked R C Enemies :-
  member (enemy_rec _ _ _ HP _ R C _ _) Enemies,
  HP > 0.

type dist_manhattan int -> int -> int -> int -> int -> o.
dist_manhattan R1 C1 R2 C2 D :-
  DR is R1 - R2, (DR >= 0, ADR = DR ; DR < 0, ADR is 0 - DR),
  DC is C1 - C2, (DC >= 0, ADC = DC ; DC < 0, ADC is 0 - DC),
  D is ADR + ADC.

% ============================================================================
% Game Initialization
% ============================================================================

type initial_grimoire list (pair int spell) -> o.
initial_grimoire
  (pr 1 (abs (t\ zap t 9)) ::
   pr 2 (abs (t\ chain (push t "south") (zap t 6))) ::
   pr 3 (aoe 2 (t\ zap t 12)) ::
   pr 4 (abs (t\ chain (drain t 5) (freeze t 1))) :: nil).

type initial_enemies list enemy_rec -> o.
initial_enemies
  (enemy_rec "warlock" "W" "Goblin Warlock" 18 18 1 4 0 (zap "player" 7) ::
   enemy_rec "elemental" "F" "Fire Elemental" 24 24 4 2 0 (zap "player" 10) ::
   enemy_rec "golem" "V" "Void Golem" 30 30 5 5 0 (chain (zap "player" 8) (push "player" "north")) :: nil).

type game_init      state -> o.
type game_init_seed int -> state -> o.

game_init_seed Seed (game_state Hero Enemies nil Seed) :-
  initial_grimoire Grim,
  Hero = hero_rec 32 32 20 20 3 3 0 Grim,
  initial_enemies Enemies.

game_init State :-
  game_init_seed 42 State.

% ============================================================================
% Higher-Order Spell Evaluation with Beta-Reduction
% ============================================================================

type apply_spell spell -> state -> state -> string -> o.

% 1. zap Target Damage
apply_spell (zap "player" Dmg) S0 S1 Msg :-
  !,
  apply_damage_to_player Dmg S0 S1 Msg.

apply_spell (zap TargetId Dmg) (game_state Hero Enemies Auras Seed) (game_state Hero NextEnemies Auras Seed) Msg :-
  member (enemy_rec TargetId _ _ HP _ _ _ _ _) Enemies,
  HP > 0, !,
  % Amplify if player has amp aura active
  (member (aura_rec "amp" _) Auras, EffDmg is Dmg + 5, AmpNote = " (Amplified! +5)" ;
   not (member (aura_rec "amp" _) Auras), EffDmg = Dmg, AmpNote = ""),
  damage_enemy TargetId EffDmg Enemies NextEnemies,
  Msg is "Arcane zap strikes " ^ TargetId ^ " for " ^ to_string EffDmg ^ " damage!" ^ AmpNote.

apply_spell (zap TargetId _) S S Msg :-
  Msg is "No valid target '" ^ TargetId ^ "' in range!".

% 2. push Target Direction
apply_spell (push "player" Dir) (game_state (hero_rec HP MHP MP MMP R C Cp Grim) En Auras Seed) (game_state (hero_rec HP MHP MP MMP NR NC Cp Grim) En Auras Seed) Msg :-
  !,
  step_pos R C Dir TR TC,
  ((in_bounds TR TC, not (is_pillar TR TC), !, NR = TR, NC = TC, Msg is "You were pushed " ^ Dir ^ "!") ;
   (NR = R, NC = C, Msg is "You were pushed against a wall!")).

apply_spell (push TargetId Dir) (game_state Hero Enemies Auras Seed) (game_state Hero NextEnemies Auras Seed) Msg :-
  member (enemy_rec TargetId G Name HP MHP R C Fr In) Enemies,
  HP > 0, !,
  step_pos R C Dir TR TC,
  ((in_bounds TR TC, not (is_pillar TR TC), not (is_blocked TR TC Enemies), !,
     NR = TR, NC = TC, Msg is "Force push sends " ^ Name ^ " flying " ^ Dir ^ "!") ;
   (NR = R, NC = C, Msg is Name ^ " slams against an obstacle and resists movement!")),
  replace_enemy TargetId (enemy_rec TargetId G Name HP MHP NR NC Fr In) Enemies NextEnemies.

apply_spell (push _ _) S S "Push had no effect.".

% 3. freeze Target Turns
apply_spell (freeze TargetId Turns) (game_state Hero Enemies Auras Seed) (game_state Hero NextEnemies Auras Seed) Msg :-
  member (enemy_rec TargetId G Name HP MHP R C _ In) Enemies,
  HP > 0, !,
  replace_enemy TargetId (enemy_rec TargetId G Name HP MHP R C Turns In) Enemies NextEnemies,
  Msg is "Frost encases " ^ Name ^ " for " ^ to_string Turns ^ " turn(s)!".

apply_spell (freeze _ _) S S "Target cannot be frozen.".

% 4. heal Target Amount
apply_spell (heal "player" Amt) (game_state (hero_rec HP MHP MP MMP R C Cp Grim) En Auras Seed) (game_state (hero_rec NHP MHP MP MMP R C Cp Grim) En Auras Seed) Msg :-
  !,
  RawHP is HP + Amt,
  clamp_int RawHP 0 MHP NHP,
  Msg is "Healing light restores " ^ to_string Amt ^ " HP!".

apply_spell (heal _ _) S S "Healing fizzles.".

% 5. drain Target Amount (Siphon HP & MP)
apply_spell (drain TargetId Amt) (game_state (hero_rec HP MHP MP MMP R C Cp Grim) Enemies Auras Seed) (game_state (hero_rec NHP MHP NMP MMP R C Cp Grim) NextEnemies Auras Seed) Msg :-
  member (enemy_rec TargetId _ _ EHP _ _ _ _ _) Enemies,
  EHP > 0, !,
  damage_enemy TargetId Amt Enemies NextEnemies,
  RawHP is HP + Amt, clamp_int RawHP 0 MHP NHP,
  RawMP is MP + 3, clamp_int RawMP 0 MMP NMP,
  Msg is "You siphon " ^ to_string Amt ^ " HP and 3 MP from " ^ TargetId ^ "!".

apply_spell (drain _ _) S S "Drain target invalid.".

% 6. chain Spell1 Spell2 (Higher-Order Sequential Composition)
apply_spell (chain S1 S2) S0 S2 Msg :-
  apply_spell S1 S0 S1 Msg1,
  apply_spell S2 S1 S2 Msg2,
  Msg is Msg1 ^ " -> " ^ Msg2.

% 7. empower Bonus Spell (Higher-Order Functor)
apply_spell (empower Bonus (zap T Dmg)) S0 S1 Msg :-
  NewDmg is Dmg + Bonus,
  apply_spell (zap T NewDmg) S0 S1 Msg.
apply_spell (empower Bonus S) S0 S1 Msg :-
  apply_spell S S0 S1 Msg.

% 8. aoe Radius (x\ S x) (Higher-Order Abstract Syntax with Beta-Reduction)
apply_spell (aoe Radius SpellFn) (game_state (hero_rec HP MHP MP MMP HR HC Cp Grim) Enemies Auras Seed) (game_state (hero_rec HP MHP MP MMP HR HC Cp Grim) NextEnemies Auras Seed) Msg :-
  resolve_aoe Radius HR HC SpellFn Enemies NextEnemies HitList,
  (HitList = nil, Msg is "The AoE expands across radius " ^ to_string Radius ^ ", but no enemies were in range!" ;
   join_with ", " HitList TargetNames, Msg is "The AoE detonates across radius " ^ to_string Radius ^ ", striking: [" ^ TargetNames ^ "]!").

% --- Higher-Order AoE Evaluator ---
type resolve_aoe int -> int -> int -> (string -> spell) -> list enemy_rec -> list enemy_rec -> list string -> o.
resolve_aoe _ _ _ _ nil nil nil.
resolve_aoe Radius HR HC SpellFn (enemy_rec ID G Name HP MHP R C Fr In :: Rest) (enemy_rec ID G Name NHP MHP R C Fr In :: OutEnemies) (Name :: OutHits) :-
  HP > 0,
  dist_manhattan HR HC R C D,
  D =< Radius, !,
  % Beta-reduction: applying SpellFn to ID at the meta-level!
  TargetedSpell = (SpellFn ID),
  extract_damage TargetedSpell Dmg,
  RawHP is HP - Dmg, clamp_int RawHP 0 MHP NHP,
  resolve_aoe Radius HR HC SpellFn Rest OutEnemies OutHits.
resolve_aoe Radius HR HC SpellFn (E :: Rest) (E :: OutEnemies) OutHits :-
  resolve_aoe Radius HR HC SpellFn Rest OutEnemies OutHits.

type extract_damage spell -> int -> o.
extract_damage (zap _ D) D :- !.
extract_damage (drain _ D) D :- !.
extract_damage (chain S _) D :- extract_damage S D, !.
extract_damage (empower B S) D :- extract_damage S Base, D is Base + B, !.
extract_damage _ 10.

% ============================================================================
% Hypothetical Aura Damage Resolution for Player
% ============================================================================

type apply_damage_to_player int -> state -> state -> string -> o.
apply_damage_to_player Dmg (game_state (hero_rec HP MHP MP MMP R C Cp Grim) En Auras Seed) SFinal Msg :-
  % Check hypothetical auras installed as logical rules:
  install_active_auras Auras
    ( ((aura_shield_reflect "player", !,
        reflect_to_first_enemy Dmg En NextEn TargetName,
        Msg = "Your Shield of Reflection glows brightly! Damage reflected to " ^ TargetName ^ "!",
        SFinal = game_state (hero_rec HP MHP MP MMP R C Cp Grim) NextEn Auras Seed)) ;
      ((aura_ward_fire "player", !,
        Msg = "Your Arcane Ward completely absorbs the incoming blast (0 damage taken)!",
        SFinal = game_state (hero_rec HP MHP MP MMP R C Cp Grim) En Auras Seed)) ;
      ( EffDmg = Dmg,
        RawHP is HP - EffDmg, clamp_int RawHP 0 MHP NHP,
        Msg = "You take " ^ to_string EffDmg ^ " direct magical damage!",
        SFinal = game_state (hero_rec NHP MHP MP MMP R C Cp Grim) En Auras Seed ) ).

type install_active_auras list aura_rec -> o -> o.
install_active_auras nil G :- G.
install_active_auras (aura_rec "ward" _ :: Rest) G :-
  (pi p\ aura_ward_fire p) => install_active_auras Rest G.
install_active_auras (aura_rec "reflect" _ :: Rest) G :-
  (pi p\ aura_shield_reflect p) => install_active_auras Rest G.
install_active_auras (aura_rec "amp" _ :: Rest) G :-
  (pi p\ aura_amp_magic p) => install_active_auras Rest G.
install_active_auras (_ :: Rest) G :-
  install_active_auras Rest G.

type reflect_to_first_enemy int -> list enemy_rec -> list enemy_rec -> string -> o.
reflect_to_first_enemy _ nil nil "the void".
reflect_to_first_enemy Dmg (enemy_rec ID G Name HP MHP R C Fr In :: Rest) (enemy_rec ID G Name NHP MHP R C Fr In :: Rest) Name :-
  HP > 0, !,
  RawHP is HP - Dmg, clamp_int RawHP 0 MHP NHP.
reflect_to_first_enemy Dmg (E :: Rest) (E :: OutRest) Target :-
  reflect_to_first_enemy Dmg Rest OutRest Target.

type damage_enemy string -> int -> list enemy_rec -> list enemy_rec -> o.
damage_enemy _ _ nil nil.
damage_enemy TargetId Dmg (enemy_rec TargetId G Name HP MHP R C Fr In :: Rest) (enemy_rec TargetId G Name NHP MHP R C Fr In :: Rest) :-
  !,
  RawHP is HP - Dmg, clamp_int RawHP 0 MHP NHP.
damage_enemy TargetId Dmg (E :: Rest) (E :: NextRest) :-
  damage_enemy TargetId Dmg Rest NextRest.

type replace_enemy string -> enemy_rec -> list enemy_rec -> list enemy_rec -> o.
replace_enemy _ _ nil nil.
replace_enemy TargetId NewE (enemy_rec TargetId _ _ _ _ _ _ _ _ :: Rest) (NewE :: Rest) :- !.
replace_enemy TargetId NewE (E :: Rest) (E :: NextRest) :-
  replace_enemy TargetId NewE Rest NextRest.

type step_pos int -> int -> string -> int -> int -> o.
step_pos R C "north" NR C :- NR is R - 1.
step_pos R C "south" NR C :- NR is R + 1.
step_pos R C "west" R NC :- NC is C - 1.
step_pos R C "east" R NC :- NC is C + 1.
step_pos R C "n" NR C :- NR is R - 1.
step_pos R C "s" NR C :- NR is R + 1.
step_pos R C "w" R NC :- NC is C - 1.
step_pos R C "e" R NC :- NC is C + 1.

% ============================================================================
% Enemy AI Turn Resolution & Higher-Order Counterspelling
% ============================================================================

type enemy_turn_step state -> state -> string -> o.
enemy_turn_step (game_state Hero Enemies Auras Seed) (game_state NextHero NextEnemies NextAuras NextSeed) Msg :-
  tick_auras Auras NextAuras,
  resolve_all_enemies Hero Enemies Auras NextHero NextEnemies EnemyNotes,
  prng_step Seed NextSeed _,
  join_with " " EnemyNotes Msg.

type tick_auras list aura_rec -> list aura_rec -> o.
tick_auras nil nil.
tick_auras (aura_rec Name Rem :: Rest) (aura_rec Name NRem :: NextRest) :-
  Rem > 1, !, NRem is Rem - 1,
  tick_auras Rest NextRest.
tick_auras (_ :: Rest) NextRest :-
  tick_auras Rest NextRest.

type resolve_all_enemies hero_rec -> list enemy_rec -> list aura_rec -> hero_rec -> list enemy_rec -> list string -> o.
resolve_all_enemies Hero nil _ Hero nil nil.
resolve_all_enemies Hero (enemy_rec ID G Name HP MHP R C Fr In :: Rest) Auras FinalHero (enemy_rec ID G Name HP MHP R C NFr In :: OutRest) (Note :: NotesRest) :-
  HP > 0, Fr > 0, !,
  NFr is Fr - 1,
  Note is Name ^ " is frozen solid and skips their turn.",
  resolve_all_enemies Hero Rest Auras FinalHero OutRest NotesRest.
resolve_all_enemies (hero_rec HHP HMHP HMP HMMP HR HC Cp Grim) (enemy_rec ID G Name HP MHP R C 0 In :: Rest) Auras FinalHero (enemy_rec ID G Name HP MHP R C 0 In :: OutRest) (Note :: NotesRest) :-
  HP > 0, dist_manhattan HR HC R C Dist, Dist =< 3, !,
  % Enemy casts innate spell. Check if player counter is primed!
  ((Cp > 0, !,
      % Counterspell primed: Higher-order pattern matching intercepts enemy spell
      decompose_enemy_spell In AbsorbedMana,
      NHMP is HMP + AbsorbedMana, clamp_int NHMP 0 HMMP FinMP,
      Note is "COUNTERSPELL! You dissected " ^ Name ^ "'s spell into raw aether and absorbed " ^ to_string AbsorbedMana ^ " MP!",
      MidHero = hero_rec HHP HMHP FinMP HMMP HR HC 0 Grim) ;
   (  % Uncountered: Resolve incoming spell
      apply_damage_to_player 8 (game_state (hero_rec HHP HMHP HMP HMMP HR HC 0 Grim) (enemy_rec ID G Name HP MHP R C 0 In :: Rest) Auras 0) (game_state MidHero _ _ _) HitMsg,
      Note is Name ^ " unleashes dark magic! " ^ HitMsg)),
  resolve_all_enemies MidHero Rest Auras FinalHero OutRest NotesRest.
resolve_all_enemies Hero (E :: Rest) Auras FinalHero (E :: OutRest) NotesRest :-
  resolve_all_enemies Hero Rest Auras FinalHero OutRest NotesRest.

% Pattern matching on enemy spell structure
type decompose_enemy_spell spell -> int -> o.
decompose_enemy_spell (zap _ Dmg) Dmg :- !.
decompose_enemy_spell (chain (zap _ Dmg) _) Dmg :- !.
decompose_enemy_spell _ 6.

% ============================================================================
% Game Step Dispatch
% ============================================================================

type game_step action -> state -> state -> string -> o.

% Action: move Dir
game_step (move Dir) (game_state (hero_rec HP MHP MP MMP R C Cp Grim) En Auras Seed) NextSt Msg :-
  step_pos R C Dir NR NC,
  in_bounds NR NC,
  not (is_pillar NR NC),
  not (is_blocked NR NC En), !,
  MidHero = hero_rec HP MHP MP MMP NR NC Cp Grim,
  enemy_turn_step (game_state MidHero En Auras Seed) NextSt EnemyMsg,
  P1 is "You move " ^ Dir ^ ". ",
  Msg is P1 ^ EnemyMsg.

% Action: cast Slot Target
game_step (cast Slot Target) (game_state (hero_rec HP MHP MP MMP R C Cp Grim) En Auras Seed) NextSt Msg :-
  lookup Slot Grim RawSpell,
  MP >= 4, !,
  NMP is MP - 4,
  ((RawSpell = abs SpellFn, !, TargetedSpell = (SpellFn Target)) ; TargetedSpell = RawSpell),
  apply_spell TargetedSpell (game_state (hero_rec HP MHP NMP MMP R C Cp Grim) En Auras Seed) StAfterSpell SpellMsg,
  enemy_turn_step StAfterSpell NextSt EnemyMsg,
  P1 is "Cast Slot " ^ to_string Slot ^ ": " ^ SpellMsg ^ " ",
  Msg is P1 ^ EnemyMsg.

% Action: cast_aoe Slot
game_step (cast_aoe Slot) (game_state (hero_rec HP MHP MP MMP R C Cp Grim) En Auras Seed) NextSt Msg :-
  lookup Slot Grim Spell,
  MP >= 6, !,
  NMP is MP - 6,
  apply_spell Spell (game_state (hero_rec HP MHP NMP MMP R C Cp Grim) En Auras Seed) StAfterSpell SpellMsg,
  enemy_turn_step StAfterSpell NextSt EnemyMsg,
  P1 is "Detonated AoE Slot " ^ to_string Slot ^ ": " ^ SpellMsg ^ " ",
  Msg is P1 ^ EnemyMsg.

% Action: craft Slot NewSpell
game_step (craft Slot NewSpell) (game_state (hero_rec HP MHP MP MMP R C Cp Grim) En Auras Seed) NextSt Msg :-
  MP >= 2, !,
  NMP is MP - 2,
  update Slot NewSpell Grim NextGrim,
  MidHero = hero_rec HP MHP NMP MMP R C Cp NextGrim,
  enemy_turn_step (game_state MidHero En Auras Seed) NextSt EnemyMsg,
  P1 is "Grimoire Slot " ^ to_string Slot ^ " re-inscribed! ",
  Msg is P1 ^ EnemyMsg.

% Action: enchant Aura Duration
game_step (enchant AuraName Dur) (game_state (hero_rec HP MHP MP MMP R C Cp Grim) En Auras Seed) NextSt Msg :-
  MP >= 5, !,
  NMP is MP - 5,
  NewAuras = (aura_rec AuraName Dur :: Auras),
  MidHero = hero_rec HP MHP NMP MMP R C Cp Grim,
  enemy_turn_step (game_state MidHero En NewAuras Seed) NextSt EnemyMsg,
  P1 is "Erected Aura of " ^ AuraName ^ " for " ^ to_string Dur ^ " turns! ",
  Msg is P1 ^ EnemyMsg.

% Action: counter (Prime counterspell reaction)
game_step counter (game_state (hero_rec HP MHP MP MMP R C _ Grim) En Auras Seed) NextSt Msg :-
  MP >= 3, !,
  NMP is MP - 3,
  MidHero = hero_rec HP MHP NMP MMP R C 1 Grim,
  enemy_turn_step (game_state MidHero En Auras Seed) NextSt EnemyMsg,
  P1 is "Counterspell primed! You ready your mind to dissect the next incoming spell. ",
  Msg is P1 ^ EnemyMsg.

% Action: meditate (Recover MP)
game_step meditate (game_state (hero_rec HP MHP MP MMP R C Cp Grim) En Auras Seed) NextSt Msg :-
  RawMP is MP + 8, clamp_int RawMP 0 MMP NMP,
  MidHero = hero_rec HP MHP NMP MMP R C Cp Grim,
  enemy_turn_step (game_state MidHero En Auras Seed) NextSt EnemyMsg,
  P1 is "You channel the ambient leylines and recover 8 MP. ",
  Msg is P1 ^ EnemyMsg.

% Action: inspect
game_step inspect S S "You attune your senses to the battlefield matrix.".

% ============================================================================
% ASCII Dual-Pane UI Rendering
% ============================================================================

type query_cell hero_rec -> list enemy_rec -> int -> int -> string -> o.
query_cell (hero_rec _ _ _ _ R C _ _) _ R C "@" :- !.
query_cell _ Enemies R C Glyph :-
  member (enemy_rec _ Glyph _ HP _ R C _ _) Enemies,
  HP > 0, !.
query_cell _ _ R C "#" :- is_pillar R C, !.
query_cell _ _ _ _ ".".

type render_arena_row hero_rec -> list enemy_rec -> int -> string -> o.
render_arena_row Hero En R Out :-
  query_cell Hero En R 1 C1,
  query_cell Hero En R 2 C2,
  query_cell Hero En R 3 C3,
  query_cell Hero En R 4 C4,
  query_cell Hero En R 5 C5,
  P1 is "| " ^ C1 ^ " " ^ C2 ^ " ",
  P2 is P1 ^ C3 ^ " " ^ C4 ^ " ",
  Out is P2 ^ C5 ^ " |".

type render_arena_lines hero_rec -> list enemy_rec -> list string -> o.
render_arena_lines Hero En Lines :-
  Div is "+-----------+",
  render_arena_row Hero En 1 R1,
  render_arena_row Hero En 2 R2,
  render_arena_row Hero En 3 R3,
  render_arena_row Hero En 4 R4,
  render_arena_row Hero En 5 R5,
  Lines = (Div :: R1 :: R2 :: R3 :: R4 :: R5 :: Div :: nil).

type format_auras list aura_rec -> string -> o.
format_auras nil "none".
format_auras (aura_rec N D :: nil) Out :-
  Out is N ^ "(" ^ to_string D ^ "t)".
format_auras (aura_rec N D :: Rest) Out :-
  format_auras Rest ROut,
  P is N ^ "(" ^ to_string D ^ "t), ",
  Out is P ^ ROut.

type format_grimoire_slot list (pair int spell) -> int -> string -> o.
format_grimoire_slot Grim 1 Out :-
  lookup 1 Grim (abs Fn), Fn "target" (zap _ Dmg), !,
  Out is "1: abs (t\\ zap t " ^ to_string Dmg ^ ")".
format_grimoire_slot Grim 1 Out :-
  lookup 1 Grim (zap _ Dmg), !,
  Out is "1: zap target " ^ to_string Dmg.
format_grimoire_slot Grim 1 Out :-
  lookup 1 Grim _, Out = "1: [custom spell]".
format_grimoire_slot Grim 2 Out :-
  lookup 2 Grim (abs Fn), Fn "target" (chain (push _ Dir) (zap _ Dmg)), !,
  Out is "2: abs (t\\ push " ^ Dir ^ " & zap " ^ to_string Dmg ^ ")".
format_grimoire_slot Grim 2 Out :-
  lookup 2 Grim (chain _ (zap _ Dmg)), !,
  Out is "2: chain push (zap " ^ to_string Dmg ^ ")".
format_grimoire_slot Grim 2 Out :-
  lookup 2 Grim _, Out = "2: [custom spell]".
format_grimoire_slot Grim 3 Out :-
  lookup 3 Grim (aoe R _), !,
  Out is "3: aoe " ^ to_string R ^ " (t\\ zap t 12)".
format_grimoire_slot Grim 3 Out :-
  lookup 3 Grim _, Out = "3: [custom spell]".
format_grimoire_slot Grim 4 Out :-
  lookup 4 Grim (abs Fn), Fn "target" (chain (drain _ Dmg) (freeze _ Turns)), !,
  Out is "4: abs (t\\ drain " ^ to_string Dmg ^ " & freeze " ^ to_string Turns ^ "t)".
format_grimoire_slot Grim 4 Out :-
  lookup 4 Grim (chain (drain _ Dmg) _), !,
  Out is "4: drain " ^ to_string Dmg ^ " + freeze 1t".
format_grimoire_slot Grim 4 Out :-
  lookup 4 Grim _, Out = "4: [custom spell]".
format_grimoire_slot _ N Out :-
  Out is to_string N ^ ": [unassigned]".

type game_render state -> string -> o.
game_render (game_state (hero_rec HP MHP MP MMP R C Cp Grim) Enemies Auras _) Out :-
  render_arena_lines (hero_rec HP MHP MP MMP R C Cp Grim) Enemies ArenaLines,
  render_panel_box "SANCTUM ARENA" 13 ArenaLines ArenaBox,

  render_bar "HP" HP MHP 8 HPBar,
  render_bar "MP" MP MMP 8 MPBar,
  format_auras Auras AuraStr,
  AuraLine is "Auras: [" ^ AuraStr ^ "]",
  (Cp > 0, CpLine = "Counter: [PRIMED]" ; CpLine = "Counter: [ready]"),

  format_grimoire_slot Grim 1 S1,
  format_grimoire_slot Grim 2 S2,
  format_grimoire_slot Grim 3 S3,
  format_grimoire_slot Grim 4 S4,

  StatusLines =
    (HPBar :: MPBar :: AuraLine :: CpLine ::
     "--- GRIMOIRE SLOTS ---" ::
     S1 :: S2 :: S3 :: S4 :: nil),
  render_panel_box "MAGUS VITALS & GRIMOIRE" 30 StatusLines StatusBox,

  h_stack_lines 17 "  " ArenaBox StatusBox CombinedLines,
  concat_lines CombinedLines ScreenBody,

  Header is "===================== THE ARCHMAGE'S GRIMOIRE =====================\n",
  Footer is "\nCommands: cast Slot Target. | cast_aoe Slot. | craft Slot Spell.\n          enchant Aura Dur.  | move Dir.      | counter. | meditate.\n",
  P1 is Header ^ ScreenBody,
  Out is P1 ^ Footer.

% ============================================================================
% Game Over Conditions
% ============================================================================

type all_enemies_dead list enemy_rec -> o.
all_enemies_dead nil.
all_enemies_dead (enemy_rec _ _ _ HP _ _ _ _ _ :: Rest) :-
  HP =< 0,
  all_enemies_dead Rest.

type game_over state -> string -> o.
game_over (game_state (hero_rec HP _ _ _ _ _ _ _) _ _ _) "DEFEAT! Your magical essence has dissipated into the void." :-
  HP =< 0, !.

game_over (game_state _ Enemies _ _) "VICTORY! The Sanctum of Glyphs is purified! All constructs vanquished!" :-
  all_enemies_dead Enemies, !.

% ============================================================================
% Game Help
% ============================================================================

type game_help string -> o.
game_help
  "The Archmage's Grimoire — Higher-Order Spellcraft\n  cast 1 \"warlock\".      Cast spell in slot 1 targeting warlock\n  cast_aoe 3.            Detonate AoE spell across radius (beta-reduces on targets)\n  craft 1 (zap \"target\" 15). Re-inscribe slot 1 with a custom spell\n  enchant \"ward\" 3.      Erect Aura of Fire Ward for 3 turns (hypothetical rule)\n  enchant \"reflect\" 3.   Erect Aura of Reflection for 3 turns\n  enchant \"amp\" 3.       Erect Aura of Amplification (+5 spell damage)\n  counter.               Prime reactive counterspell to dissect next enemy attack\n  move \"north\".          Move Magus (\"n\", \"s\", \"e\", \"w\")\n  meditate.              Meditate to restore 8 MP\n  :undo, :restart        Game engine shell commands\n".

% ============================================================================
% Embedded Verification Queries
% ============================================================================

query succeeds ? game_init S.
query succeeds ? initial_grimoire G, lookup 1 G (abs (t\ zap t 9)).
query succeeds ?
  game_init S0,
  game_step (move "north") S0 S1 Msg1,
  game_step (cast 1 "warlock") S1 S2 Msg2.
query succeeds ?
  game_init S0,
  game_step (cast_aoe 3) S0 S1 MsgAoE.
query succeeds ?
  game_init S0,
  game_step counter S0 S1 MsgCounter.
query succeeds ?
  game_init S0,
  game_render S0 Out.
