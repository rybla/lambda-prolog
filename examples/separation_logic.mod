% title: Separation Logic & Local Heap Reasoning
% tags: separation-logic, heap, points-to, separating-conjunction, frame-rule
% summary: Separation logic following O'Hearn, Reynolds, and Yang for local reasoning
%   about mutable heaps. Implements points-to assertions (l ↦ v), the empty heap
%   assertion (emp), spatial separating conjunction (P ∗ Q) via disjoint heap
%   partitioning, the Frame Rule, and verification of pointer mutations and swaps.

module separation_logic.

% ============================================================================
% Heap Locations, Values, and Disjoint Partitions
% ============================================================================

kind loc type.
kind hval type.

type loc_id   int -> loc.
type v_int    int -> hval.
type v_null   hval.

kind cell type.
type m_cell   loc -> hval -> cell.

type heap list cell.

% ============================================================================
% Spatial Assertions
% ============================================================================

kind s_assert type.

% Empty heap: emp holds only when the heap domain is empty
type emp       s_assert.

% Points-to predicate: l ↦ v (singleton heap where location l contains value v)
type points_to loc -> hval -> s_assert.

% Separating conjunction: P ∗ Q
% Holds if the heap can be split into two disjoint sub-heaps h1 and h2
% such that h1 satisfies P and h2 satisfies Q.
type star      s_assert -> s_assert -> s_assert.

% Classical conjunction (for pure assertions)
type s_and     s_assert -> s_assert -> s_assert.

% ============================================================================
% Disjoint Heap Splitting: heap_split H H1 H2  (H = H1 ⊎ H2)
% ============================================================================

type heap_split list cell -> list cell -> list cell -> o.

heap_split nil nil nil.
heap_split (C :: Rest) (C :: H1) H2 :-
  heap_split Rest H1 H2.
heap_split (C :: Rest) H1 (C :: H2) :-
  heap_split Rest H1 H2.

% Distinct location check to ensure well-formed heaps (no duplicate addresses):
type no_dup_locs list cell -> o.
type loc_not_in  loc -> list cell -> o.

no_dup_locs nil.
no_dup_locs (m_cell L _ :: Rest) :-
  loc_not_in L Rest,
  no_dup_locs Rest.

loc_not_in _ nil.
loc_not_in L (m_cell L' _ :: Rest) :-
  not (L = L'),
  loc_not_in L Rest.

% ============================================================================
% Assertion Satisfaction: sat_sep Heap Assertion
% ============================================================================

type sat_sep list cell -> s_assert -> o.

% emp holds on the strictly empty heap:
sat_sep nil emp.

% l ↦ v holds on a singleton heap containing exactly location L with value V:
sat_sep (m_cell L V :: nil) (points_to L V).

% P ∗ Q holds if heap H splits into disjoint H1 and H2 satisfying P and Q:
sat_sep H (star P Q) :-
  heap_split H H1 H2,
  sat_sep H1 P,
  sat_sep H2 Q.

% Pure conjunction:
sat_sep H (s_and P Q) :-
  sat_sep H P,
  sat_sep H Q.

% ============================================================================
% Heap Commands and Operational Step
% ============================================================================

kind h_cmd type.
type h_store  loc -> hval -> h_cmd.       % [L] := V
type h_swap   loc -> loc -> h_cmd.        % swap contents of L1 and L2
type h_seq    h_cmd -> h_cmd -> h_cmd.

% Execute a heap command: exec_heap InHeap Command OutHeap
type exec_heap list cell -> h_cmd -> list cell -> o.
type cell_update list cell -> loc -> hval -> list cell -> o.
type cell_lookup list cell -> loc -> hval -> o.

cell_lookup (m_cell L V :: _) L V :- !.
cell_lookup (_ :: Rest) L V :- cell_lookup Rest L V.

cell_update (m_cell L _ :: Rest) L V (m_cell L V :: Rest) :- !.
cell_update (C :: Rest) L V (C :: OutRest) :-
  cell_update Rest L V OutRest.

% Store: updates location L in heap
exec_heap In (h_store L V) Out :-
  cell_lookup In L _,
  cell_update In L V Out.

% Swap: swaps values at L1 and L2
exec_heap In (h_swap L1 L2) Out :-
  cell_lookup In L1 V1,
  cell_lookup In L2 V2,
  cell_update In L1 V2 Mid,
  cell_update Mid L2 V1 Out.

% Sequence:
exec_heap In (h_seq C1 C2) Out :-
  exec_heap In C1 Mid,
  exec_heap Mid C2 Out.

% ============================================================================
% Separation Logic Triples & The Frame Rule
% ============================================================================

% Small-footprint specification: {P} C {Q}
% Every heap satisfying P can safely execute C and produce a heap satisfying Q.
type sep_triple s_assert -> h_cmd -> s_assert -> o.

% Store specification:
% {L ↦ _} [L] := V {L ↦ V}
sep_triple (points_to L _) (h_store L V) (points_to L V).

% Swap specification:
% {L1 ↦ V1 ∗ L2 ↦ V2} swap(L1, L2) {L1 ↦ V2 ∗ L2 ↦ V1}
sep_triple (star (points_to L1 V1) (points_to L2 V2))
           (h_swap L1 L2)
           (star (points_to L1 V2) (points_to L2 V1)).

% Sequence rule:
sep_triple P (h_seq C1 C2) Q :-
  sep_triple P C1 Mid,
  sep_triple Mid C2 Q.

% Frame Rule Verification:
%
%      {P} C {Q}
% -------------------- (Frame Rule)
%  {P ∗ R} C {Q ∗ R}
%
% Verifies that if C runs on the active footprint satisfying P to produce Q,
% any disjoint frame R remains completely unmodified.
type app_cells list cell -> list cell -> list cell -> o.
app_cells nil L L.
app_cells (X :: Xs) Ys (X :: Zs) :-
  app_cells Xs Ys Zs.

type verify_frame list cell -> s_assert -> h_cmd -> s_assert -> s_assert -> o.
verify_frame InH P Cmd Q FrameR :-
  sat_sep InH (star P FrameR),
  heap_split InH ActiveH FrameH,
  sat_sep ActiveH P,
  sat_sep FrameH FrameR,
  exec_heap ActiveH Cmd ActiveH',
  sat_sep ActiveH' Q,
  app_cells ActiveH' FrameH OutH,
  sat_sep OutH (star Q FrameR).

% ============================================================================
% Example Queries
% ============================================================================

% Singleton points-to satisfaction: [loc 1 ↦ 10] ⊨ (loc 1 ↦ 10)
query succeeds ?
  sat_sep (m_cell (loc_id 1) (v_int 10) :: nil)
          (points_to (loc_id 1) (v_int 10)).

% Separating conjunction requires disjoint locations:
% [loc 1 ↦ 10, loc 2 ↦ 20] ⊨ (loc 1 ↦ 10) ∗ (loc 2 ↦ 20)
query succeeds ?
  sat_sep (m_cell (loc_id 1) (v_int 10) :: m_cell (loc_id 2) (v_int 20) :: nil)
          (star (points_to (loc_id 1) (v_int 10))
                (points_to (loc_id 2) (v_int 20))).

% Aliasing failure: A single memory cell CANNOT satisfy (l ↦ 10 ∗ l ↦ 10)
% because the separating conjunction requires disjoint heap partitions!
query fails ?
  sat_sep (m_cell (loc_id 1) (v_int 10) :: nil)
          (star (points_to (loc_id 1) (v_int 10))
                (points_to (loc_id 1) (v_int 10))).

% Pointer swap specification check:
% {L1 ↦ 100 ∗ L2 ↦ 200} swap(L1, L2) {L1 ↦ 200 ∗ L2 ↦ 100}
query succeeds ?
  sep_triple (star (points_to (loc_id 1) (v_int 100))
                   (points_to (loc_id 2) (v_int 200)))
             (h_swap (loc_id 1) (loc_id 2))
             (star (points_to (loc_id 1) (v_int 200))
                   (points_to (loc_id 2) (v_int 100))).

% Frame Rule in action:
% Active footprint: L1 ↦ 100. Command: [L1] := 999.
% Frame: L2 ↦ 555.
% Result heap satisfies {L1 ↦ 999 ∗ L2 ↦ 555}.
query succeeds ?
  H = (m_cell (loc_id 1) (v_int 100) :: m_cell (loc_id 2) (v_int 555) :: nil),
  verify_frame H
    (points_to (loc_id 1) (v_int 100))
    (h_store (loc_id 1) (v_int 999))
    (points_to (loc_id 1) (v_int 999))
    (points_to (loc_id 2) (v_int 555)).
