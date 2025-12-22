import ChipFiringWithLean.Config
import Paperproof

set_option linter.unusedVariables false
set_option trace.split.failure true
set_option linter.unusedSectionVars false

open Multiset Finset

-- Assume V is a finite type with decidable equality
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]

/-- An orientation of a graph assigns a direction to each edge.
    The consistent field ensures each undirected edge corresponds to exactly
    one directed edge in the orientation. -/
structure CFOrientation (G : CFGraph V) :=
  /-- The set of directed edges in the orientation -/
  (directed_edges : Multiset (V × V))
  /-- Preserves edge counts between vertex pairs -/
  (count_preserving : ∀ v w,
    num_edges G v w =
    Multiset.count (v, w) directed_edges + Multiset.count (w, v) directed_edges)
  /-- No bidirectional edges in the orientation -/
  (no_bidirectional : ∀ v w,
    Multiset.count (v, w) directed_edges = 0 ∨
    Multiset.count (w, v) directed_edges = 0)

abbrev flow {G: CFGraph V} (O : CFOrientation G) (u v : V) : ℕ :=
  Multiset.count (u,v) O.directed_edges

lemma opp_flow {G : CFGraph V} (O : CFOrientation G) (u v : V) :
  flow O u v + flow O v u= (num_edges G u v) := by
  rw[O.count_preserving u v]

lemma eq_orient {G : CFGraph V} (O1 O2 : CFOrientation G) : O1 = O2 ↔ ∀ (u v : V), flow O1 u v = flow O2 u v := by
  constructor
  · intro h_eq u v
    rw [h_eq]
  -- Converse
  · intro h_flow_eq
    have h_directed_edges_eq : O1.directed_edges = O2.directed_edges := by
      apply Multiset.ext.mpr
      intro ⟨u,v⟩
      specialize h_flow_eq u v
      exact h_flow_eq
    cases O1
    cases O2
    cases h_directed_edges_eq
    rfl

/-- Helper lema for the count below.-/
lemma double_sum (f : V × V → ℕ) : ∑  (u : V), ∑ (v : V), f ⟨u,v⟩ = ∑ (e : V × V), f e := by
  rw [← Finset.sum_product]
  simp

/-- Helper lemma for later calculations. Puzzlingly
  intricate for such a simple statement! Perhaps it can
  be simplified. -/
lemma card_directed_edges_eq_card_edges {G : CFGraph V} (O : CFOrientation G) : Multiset.card  O.directed_edges = Multiset.card G.edges := by
  have hms (M : Multiset (V × V)): ∀ e ∈ M, e ∈ univ := by
      intro e _
      exact mem_univ e

  let f (u v : V) := flow O u v
  let g (u v : V) := Multiset.count ⟨u,v⟩ G.edges
  have h_uv (u v : V) : f u v + f v u = g u v + g v u := by
    have h := O.count_preserving u v
    dsimp [f,g, flow]
    dsimp [num_edges] at h
    rw [← h]
    rw [← Multiset.sum_count_eq_card (hms ((Multiset.filter (fun e ↦ e = (u, v) ∨ e = (v, u)) G.edges)))]
    -- Now simplif the count of a in the filtered multiset
    have h_msum (u v : V) : Multiset.filter (λ e => e = (u, v) ∨ e = (v, u)) G.edges = Multiset.filter (λ e => e = ⟨u,v⟩) G.edges + Multiset.filter (λ e => e = ⟨v,u⟩) G.edges := by
      apply Multiset.ext.mpr
      intro e
      simp only [Multiset.count_add]
      repeat rw [Multiset.count_filter]
      by_cases h_e : e = ⟨u,v⟩
      · -- case: e = ⟨u,v⟩
        simp [h_e]
        intro h_eq _
        rw [h_eq]
        exact (isLoopless_prop_bool_equiv G.edges).mpr G.loopless v
      · -- case: e ≠ ⟨u,v⟩
        by_cases h_e' : e = ⟨v,u⟩
        · -- case: e = ⟨v,u⟩
          simp [h_e']
          intro h_eq _
          rw [h_eq]
          exact (isLoopless_prop_bool_equiv G.edges).mpr G.loopless u
        · -- case: e ≠ ⟨v,u⟩
          simp [h_e, h_e']
    rw [h_msum]
    simp only [Multiset.count_add]
    rw [sum_add_distrib]
    simp [Multiset.count_filter]
  have lhs : ∑ u: V, ∑ v : V, (f u v + f v u)= 2 * Multiset.card O.directed_edges := by
    simp only [Finset.sum_add_distrib]
    dsimp [f, flow]
    nth_rewrite 2 [Finset.sum_comm]
    rw [← two_mul]
    have h_replace := double_sum (λ e : V × V => Multiset.count e O.directed_edges)
    simp only [h_replace]
    simp
  have rhs : ∑ u : V, ∑ v : V, (g u v + g v u) = 2 * Multiset.card G.edges := by
    simp only [Finset.sum_add_distrib]
    dsimp [g, num_edges]
    nth_rewrite 2 [Finset.sum_comm]
    rw [← two_mul]
    have h_replace := double_sum (λ e : V × V => Multiset.count e G.edges)
    simp only [h_replace]
    simp
  simp only [h_uv] at lhs
  rw [lhs] at rhs
  linarith

/-- Number of edges directed into a vertex under an orientation -/
def indeg (G : CFGraph V) (O : CFOrientation G) (v : V) : ℕ :=
  Multiset.card (O.directed_edges.filter (λ e => e.snd = v))

lemma indeg_eq_sum_flow {G : CFGraph V} (O : CFOrientation G) (v : V) :
  indeg G O v = ∑ w : V, flow O w v := by
  dsimp [indeg, flow]
  suffices h_eq : (∀ S : Multiset (V × V) , ∀ v : V,
    Multiset.card (S.filter (λ e => e.snd = v)) = ∑ u : V, Multiset.count (u, v) S) by
    exact h_eq O.directed_edges v
  -- Prove by induction on the set of directed edges, following the pattern of the proof of
  -- degree_eq_total_flow in Basic.lean. I suspect the two can be unified.
  intro S v
  induction S using Multiset.induction_on with
  | empty =>
    simp only [Multiset.filter_zero, Multiset.card_zero]
    simp [Finset.sum_const_zero]
  | cons e S ih =>
    simp only [Multiset.filter_cons, Multiset.card_add, sum_add_distrib, Multiset.count_cons]
    rw [ih]
    nth_rewrite 1 [add_comm]
    apply add_left_cancel_iff.mpr
    obtain ⟨eu,ev⟩ := e
    by_cases h_ev_eq_v : ev = v
    · -- Case ev = v
      rw [h_ev_eq_v]
      simp
    · -- Case ev ≠ v
      rw [if_neg h_ev_eq_v, Multiset.card_zero]
      -- Flip the sides of the equation in the goal
      have : ∑ x : V, (if (x, v) = (eu, ev) then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        simp
        intro _
        contrapose! h_ev_eq_v
        rw [h_ev_eq_v]
      -- refine Finset.sum_eq_zero ?_
      rw [this]


/-- Number of edges directed out of a vertex under an orientation -/
def outdeg (G : CFGraph V) (O : CFOrientation G) (v : V) : ℕ :=
  Multiset.card (O.directed_edges.filter (λ e => e.fst = v))

/-- A vertex is a source if it has no incoming edges (indegree = 0) -/
def is_source (G : CFGraph V) (O : CFOrientation G) (v : V) : Bool :=
  indeg G O v = 0

/-- A vertex is a sink if it has no outgoing edges (outdegree = 0) -/
def is_sink (G : CFGraph V) (O : CFOrientation G) (v : V) : Bool :=
  outdeg G O v = 0

/-- Helper function to check if two consecutive vertices form a directed edge -/
def is_directed_edge (G : CFGraph V) (O : CFOrientation G) (u v : V) : Bool :=
  (u, v) ∈ O.directed_edges

-- Proposition verson of is_directed_edge
def directed_edge (G : CFGraph V) (O : CFOrientation G) (u v : V) : Prop :=
  (u, v) ∈ O.directed_edges

lemma nonsource_has_parent {G : CFGraph V} (O : CFOrientation G) (v : V) :
  ¬ is_source G O v → ∃ u : V, directed_edge G O u v := by
  intro h_not_source
  contrapose! h_not_source with h_no_parents
  dsimp [is_source]
  dsimp [indeg]
  simp
  apply Multiset.eq_zero_iff_forall_not_mem.mpr
  intro ⟨u,w⟩ h_uv_in_edges
  simp at h_uv_in_edges
  obtain ⟨h_mem, h_eq_wv⟩ := h_uv_in_edges
  rw [h_eq_wv] at h_mem
  specialize h_no_parents u
  contradiction

/-- Helper function for safe list access -/
def list_get_safe {α : Type} (l : List α) (i : Nat) : Option α :=
  l.get? i

/-- A directed path in a graph under an orientation -/
structure DirectedPath {G : CFGraph V} (O : CFOrientation G) where
  /-- The sequence of vertices in the path -/
  vertices : List V
  /-- Path must not be empty (at least one vertex) -/
  non_empty : vertices.length > 0
  /-- Every consecutive pair forms a directed edge -/
  valid_edges : List.Chain' (directed_edge G O) vertices

def non_repeating {G: CFGraph V} {O : CFOrientation G} (p : DirectedPath O) : Prop :=
  p.vertices.Nodup

lemma path_length_bound {G : CFGraph V} {O : CFOrientation G} (p : DirectedPath O) :
  non_repeating p → p.vertices.length ≤ Fintype.card V := by
  intro h_distinct
  have h_injective := List.nodup_iff_injective_get.mp h_distinct
  have h_card := Fintype.card_le_of_injective p.vertices.get h_injective
  refine le_trans ?_ h_card
  simp

/-- An orientation is acyclic if it has no directed cycles and
    maintains consistent edge directions between vertices -/
def is_acyclic (G : CFGraph V) (O : CFOrientation G) : Prop :=
  ∀ (p : DirectedPath O), non_repeating p

/-- The set of ancestors of a vertex v (nodes x such that there is a path x -> ... -> v) -/
noncomputable def ancestors (G : CFGraph V) (O : CFOrientation G) (v : V) : Finset V :=
  let R : V → V → Prop := fun a b => is_directed_edge G O a b = true
  open Classical in univ.filter (fun x => Relation.TransGen R x v)

/-- Measure for vertex_level termination: number of ancestors. -/
noncomputable def vertexLevelMeasure (G : CFGraph V) (O : CFOrientation G) (v : V) : Nat :=
  (ancestors G O v).card

/-- Vertices that are not sources must have at least one incoming edge. -/
lemma indeg_ge_one_of_not_source (G : CFGraph V) (O : CFOrientation G) (v : V) :
    ¬ is_source G O v → indeg G O v ≥ 1 := by
  intro h_not_source -- h_not_source : is_source G O v = false
  unfold is_source at h_not_source -- h_not_source : (decide (indeg G O v = 0)) = false
  apply Nat.one_le_iff_ne_zero.mpr -- Goal is indeg G O v ≠ 0
  intro h_eq_zero -- Assume indeg G O v = 0
  have h_decide_true : decide (indeg G O v = 0) = true := by
    rw [h_eq_zero]
    exact decide_eq_true rfl
  rw [h_decide_true] at h_not_source
  simp at h_not_source

/-- For vertices that are not sources, indegree - 1 is non-negative. -/
lemma indeg_minus_one_nonneg_of_not_source (G : CFGraph V) (O : CFOrientation G) (v : V) :
    ¬ is_source G O v → 0 ≤ (indeg G O v : ℤ) - 1 := by
  intro h_not_source
  have h_indeg_ge_1 : indeg G O v ≥ 1 := indeg_ge_one_of_not_source G O v h_not_source
  apply Int.sub_nonneg_of_le
  exact Nat.cast_le.mpr h_indeg_ge_1

/-- Configuration associated with a source vertex q under orientation O.
    Requires O to be acyclic and q to be the unique source.
    For each vertex v ≠ q, assigns indegree(v) - 1 chips. Assumes q is the unique source. -/
def config_of_source {G : CFGraph V} {O : CFOrientation G} {q : V}
    (h_acyclic : is_acyclic G O) (h_unique_source : ∀ w, is_source G O w → w = q) : Config V q :=
  { vertex_degree := λ v => if v = q then 0 else (indeg G O v : ℤ) - 1,
    q_zero := by simp
    non_negative := by
      intro v
      simp [vertex_degree]
      split_ifs with h_eq
      · linarith
      · have h_not_source : ¬ is_source G O v := by
          intro hs_v
          exact h_eq (h_unique_source v hs_v)
        exact indeg_minus_one_nonneg_of_not_source G O v h_not_source
  }

/-- The divisor associated with an orientation assigns indegree - 1 to each vertex -/
def ordiv (G : CFGraph V) (O : CFOrientation G) : CFDiv V :=
  λ v => indeg G O v - 1

def orqed {G : CFGraph V} (O : CFOrientation G) {q : V} (h_acyclic : is_acyclic G O)
    (h_unique_source : ∀ w, is_source G O w → w = q) : q_eff_div V q := {
      D := ordiv G O,
      h_eff := by
        intro v v_ne_q
        dsimp [ordiv]
        contrapose! v_ne_q with v_q
        have h_indeg : indeg G O v = 0 := by
          linarith
        specialize h_unique_source v
        rw [indeg_eq_sum_flow] at h_indeg
        -- Sum of non-negative terms is zero, so each term is zero
        apply h_unique_source
        contrapose! h_indeg with h_not_source
        dsimp [is_source] at h_not_source
        rw [indeg_eq_sum_flow] at h_not_source
        intro h_bad
        rw [h_bad] at h_not_source
        simp at h_not_source
    }

/-- Given an acyclic orientation O with a unique source q, returns a configuration c(O) -/
def orientation_to_config (G : CFGraph V) (O : CFOrientation G) (q : V)
    (h_acyclic : is_acyclic G O) (h_unique_source : ∀ w, is_source G O w → w = q) : Config V q :=
  config_of_source h_acyclic h_unique_source

/-- Compatibility between configurations and divisors from
  an orientation -/
lemma config_and_divisor_from_O {G : CFGraph V} (O : CFOrientation G) {q : V} (h_acyclic : is_acyclic G O) (h_unique_source : ∀ w, is_source G O w → w = q) :
  orientation_to_config G O q h_acyclic h_unique_source = toConfig (orqed O h_acyclic h_unique_source) := by
  let c := orientation_to_config G O q h_acyclic h_unique_source
  let D := orqed O h_acyclic h_unique_source
  rw [eq_config_iff_eq_vertex_degree]
  funext v
  by_cases h_v: v = q
  · -- Case v = q
    rw [h_v]
    have (c d : Config V q) : c.vertex_degree q = d.vertex_degree q := by
      rw [c.q_zero, d.q_zero]
    rw [this]
  · -- Case v ≠ q
    dsimp [orientation_to_config, toConfig, config_of_source, orqed, ordiv]
    simp [h_v]


/-- Helper lemma to simplify handshking argument. Is something
  like this already in Mathlib somewhere? -/
lemma sum_filter_eq_map (G : CFGraph V) (M : Multiset (V × V)) (crit  : V → V × V → Prop)
    [∀ v e, Decidable (crit v e)] :
  ∑ v : V, Multiset.card (M.filter (crit v))
    = Multiset.sum (M.map (λ e => (Finset.univ.filter (λ v => (crit v e) )).card)) := by
  -- Define P and g using Prop for clarity in the proof - Available throughout
  let P : V → V × V → Prop := fun v e => crit v e
  let g : V × V → ℕ := fun e => (Finset.univ.filter (P · e)).card

  -- Rewrite the goal using P and g for proof readability
  suffices goal_rewritten : ∑ v : V, Multiset.card (M.filter (P v)) = Multiset.sum (M.map g) by
    exact goal_rewritten -- The goal is now exactly the statement `goal_rewritten`

  -- Prove the rewritten goal by induction on the multiset G.edges
  induction M using Multiset.induction_on with
  | empty =>
    simp only [Multiset.filter_zero, Multiset.card_zero, Finset.sum_const_zero,
               Multiset.map_zero, Multiset.sum_zero] -- Use _zero lemmas
  | cons e_head s_tail ih_s_tail =>
    -- Rewrite RHS: sum(map(g, e_head::s_tail)) = g e_head + sum(map(g, s_tail))
    rw [Multiset.map_cons, Multiset.sum_cons]

    -- Rewrite LHS: ∑ v, card(filter(P v, e_head::s_tail))
    simp_rw [← Multiset.countP_eq_card_filter]
    simp only [Multiset.countP_cons]
    rw [Finset.sum_add_distrib]

    -- Simplify the second sum (∑ v, ite (P v e_head) 1 0) to g e_head
    have h_sum_ite_eq_card : ∑ v : V, ite (P v e_head) 1 0 = g e_head := by
      rw [← Finset.card_filter] -- This completes the proof for h_sum_ite_eq_card
    rw [h_sum_ite_eq_card]

    simp_rw [Multiset.countP_eq_card_filter]
    rw [add_comm, ih_s_tail]




lemma subset_source (G : CFGraph V) (O : CFOrientation G) (S : Finset V):
  S.Nonempty → is_acyclic G O → ∃ v ∈ S, ∀ w ∈ S, flow O w v = 0 := by
  intro S_nonempty h_acyclic
  by_contra! no_sourceless

  let S_path (p : DirectedPath O) : Prop :=
    ∀ v ∈ p.vertices, v ∈ S

  have arb_path (n : ℕ) : ∃ (p : DirectedPath O), S_path p ∧ p.vertices.length = n + 1:= by
    induction' n with n ih
    · -- Base case: n = 0
      -- Create a list consisting of v only
      rcases S_nonempty with ⟨v, h_v_in_S⟩
      use {
        vertices := [v],
        non_empty := by
          simp,
        valid_edges := by
          simp
      }
      simp
      intro u h_u_in_path
      rw [List.mem_singleton] at h_u_in_path
      rw [h_u_in_path]
      exact h_v_in_S
    · -- Inductive step: assume true for n, prove for n + 1
      rcases ih with ⟨p, h_len⟩
      cases hp: p.vertices with
      | nil =>
        -- This case should not happen since p.vertices has length n + 1 ≥ 1
        exfalso
        rw [hp] at h_len
        simp at h_len
      | cons v p' =>
        specialize no_sourceless v
        have v_S : v ∈ S := h_len.1 v (by simp [hp])
        rcases (no_sourceless v_S) with h_no_parent
        rcases h_no_parent with ⟨u, h_u⟩
        let new_path : List V := u :: p.vertices
        use {
          vertices := new_path,
          non_empty := by
            rw [List.length_cons]
            exact Nat.succ_pos _,
          valid_edges := by
            dsimp [new_path, List.Chain']
            cases h_case : p.vertices with
            | nil =>
              -- Path was just [v], so new path is [u, v]
              simp [hp]
            | cons v' vs =>
              have eq_vv': v = v' := by
                rw [h_case] at hp
                simp at hp
                obtain ⟨h,_⟩ := hp
                rw [h]
              rw [← eq_vv']
              constructor
              -- Show the new first link is a directed edge
              have := h_u.2
              dsimp [flow] at this
              contrapose! this with h_no_edge
              simp [h_no_edge]
              exact h_no_edge
              -- Now show the rest of the path is valid
              have h_rec := p.valid_edges
              rw [h_case] at h_rec
              rw [← eq_vv'] at h_rec
              exact h_rec
        }
        -- Should that the path lies in S
        constructor
        intro v h_v_in_path
        simp at h_v_in_path
        dsimp [new_path] at h_v_in_path
        cases h_v_in_path with
        | head h_eq_v =>
          exact h_u.1
        | tail _ h_v_in_tail =>
          exact h_len.1 v h_v_in_tail
        -- Show the length is n + 2
        rw [List.length_cons]
        rw [h_len.2]
  specialize arb_path (Fintype.card V)
  rcases arb_path with ⟨p, h_len⟩
  have ineq := path_length_bound p (h_acyclic p)
  linarith

/-- Lemma: A non-empty graph with an acyclic orientation must have at least one source. -/
lemma helper_acyclic_has_source (G : CFGraph V) (O : CFOrientation G) :
  is_acyclic G O → ∃ v : V, is_source G O v := by
  intro h_acyclic
  have h := subset_source G O Finset.univ Finset.univ_nonempty h_acyclic
  rcases h with ⟨v, _, h_source⟩
  use v
  dsimp [is_source]
  simp
  rw [indeg_eq_sum_flow]
  apply Finset.sum_eq_zero
  exact h_source

lemma is_source_of_unique_source {G : CFGraph V} (O : CFOrientation G) {q : V} (h_acyclic : is_acyclic G O)
    (h_unique_source : ∀ w, is_source G O w → w = q) :
  is_source G O q := by
  rcases helper_acyclic_has_source G O h_acyclic with ⟨q', h_q'⟩
  specialize h_unique_source q'
  have := h_unique_source h_q'
  rw [this] at h_q'
  exact h_q'

/-- Lemma: An orientation divisor has degree g-1. This is
  surprisingly tricky to implement in Lean. The proof here
  follows the same pattern as the handshaking theorem
  helper_sum_vertex_degrees, and perahps could be unified
  with it. -/
lemma degree_ordiv {G : CFGraph V} (O : CFOrientation G) :
  deg (ordiv G O) = (genus G) - 1 := by
  have flow_sum : deg (ordiv G O) = (∑ v : V, ∑ w : V, ↑(flow O w v)) - (Fintype.card V) := by
    calc
      deg (ordiv G O)
        = ∑ v : V, ordiv G O v := by rfl
      _ = ∑ v : V, (∑ w : V, ↑(flow O w v) - 1) := by
        apply Finset.sum_congr rfl
        intro x _
        dsimp [ordiv]
        rw [indeg_eq_sum_flow O x]
        simp
      _ = (∑ v : V, ∑ w : V, ↑(flow O w v)) - (Fintype.card V) := by
        rw [Finset.sum_sub_distrib]
        simp
  dsimp [genus]
  rw [flow_sum]
  suffices h : (∑ v : V, ∑ w : V, ↑(flow O w v)) = ↑(Multiset.card G.edges) by linarith [h]
  calc
    ∑ v : V, ∑ w : V, ↑(flow O w v)
      = ∑ v : V, (indeg G O v) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [indeg_eq_sum_flow]
    _ = ∑ v : V, Multiset.card (O.directed_edges.filter (λ e => e.snd = v)) := by
      dsimp [indeg]
    _ = Multiset.sum (O.directed_edges.map (λ e => (Finset.univ.filter (λ v => e.snd = v)).card)) := by
      exact (sum_filter_eq_map G O.directed_edges (λ v e => e.snd = v))
    _ = ↑(Multiset.card O.directed_edges) := by
      have h_singleton : ∀ e ∈ O.directed_edges, (Finset.filter (fun v ↦ e.2 = v) univ).card = 1  := by
        intro e h_e
        refine Finset.card_eq_one.mpr ?_
        use e.2
        refine eq_singleton_iff_unique_mem.mpr ?h.a
        constructor
        simp
        intro x h_x
        rw [Finset.mem_filter] at h_x
        rw [h_x.2]
      rw [Multiset.map_congr rfl h_singleton]
      rw [Multiset.map_const', Multiset.sum_replicate,Nat.nsmul_eq_mul, mul_one]
    _ = ↑(Multiset.card G.edges) := by
      exact card_directed_edges_eq_card_edges O
    _ = Multiset.card G.edges := by
      rfl

lemma config_degree_from_O {G : CFGraph V} (O : CFOrientation G) {q : V} (h_acyclic : is_acyclic G O) (h_unique_source : ∀ w, is_source G O w → w = q) :
  config_degree (orientation_to_config G O q h_acyclic h_unique_source) = genus G := by
  have : orientation_to_config G O q h_acyclic h_unique_source =
         toConfig (orqed O h_acyclic h_unique_source) := by
    exact config_and_divisor_from_O O h_acyclic h_unique_source
  rw [this]
  dsimp [config_degree, toConfig, orqed, ordiv]
  simp
  rw [degree_ordiv]
  simp
  -- Need to show that q *is* a source. May want to separate this into a reusable lemma.
  have h_q_source : is_source G O q := by
    exact is_source_of_unique_source O h_acyclic h_unique_source
  dsimp [is_source] at h_q_source
  simp at h_q_source
  exact h_q_source

lemma ordiv_unwinnable (G : CFGraph V) (O : CFOrientation G) :
  is_acyclic G O → ¬ winnable G (ordiv G O) := by
  intro h_acyclic
  by_contra h_win
  let D := ordiv G O
  rcases h_win with ⟨E, E_eff, E_equiv⟩
  dsimp [Div_plus] at E_eff
  dsimp [linear_equiv] at E_equiv
  rw [principal_iff_eq_prin] at E_equiv
  rcases E_equiv with ⟨σ, h_σ⟩
  apply eq_add_of_sub_eq at h_σ

  let σvals := Finset.univ.image σ
  have h_nonempty : σvals.Nonempty :=
    Finset.image_nonempty.mpr Finset.univ_nonempty
  let v_max := Finset.max' σvals h_nonempty

  have : ∃ v : V, ∀ w : V, σ w ≤ σ v := by
    have : v_max ∈ σvals := Finset.max'_mem σvals h_nonempty
    dsimp [σvals] at this
    have : ∃ v : V, σ v = v_max := by
      rw [Finset.mem_image] at this
      rcases this with ⟨v, _, h_eq⟩
      use v
    rcases this with ⟨v, h_v⟩
    use v
    intro w
    have : σ w ∈ σvals := Finset.mem_image.mpr ⟨w, Finset.mem_univ w, rfl⟩
    have := Finset.le_max' σvals (σ w) this
    rw [h_v]
    exact this

  rcases this with ⟨v_max, h_max⟩
  let S := {v : V | σ v = σ v_max}
  have S_nonempty : S.Nonempty := by
    use v_max
    simp [S]

  have h_lt (u : V) (h_u : u ∉ S):  σ u ≤ σ v_max - 1 := by
    specialize h_max u
    suffices σ u < σ v_max by linarith
    apply lt_of_le_of_ne h_max
    simp [S, Set.mem_toFinset] at h_u
    exact h_u

  suffices h_v : ∃ v ∈ S, ∀ w : V, flow O w v > 0 → w ∉ S by
    rcases h_v with ⟨v, h_v, h_flow⟩
    have h_prin : (prin G) σ v + indeg G O v ≤ 0 := by
      dsimp [prin]
      rw [indeg_eq_sum_flow O v]
      have h_diff : ∀ u : V, σ u - σ v ≤ if u ∈ S then 0 else -1 := by
        intro u
        by_cases h_u_in_S : u ∈ S
        · simp [h_u_in_S]
          -- Goal is now: σ u ≤ σ v
          dsimp [S] at h_u_in_S h_v
          rw [h_u_in_S,h_v]
        · simp [h_u_in_S]
          -- Goal is now: σ u - σ v ≤ -1
          dsimp [S] at h_u_in_S h_v
          have := h_lt u h_u_in_S
          rw [h_v]
          linarith [this]
      have h_diff_mul : ∀ u : V, (σ u - σ v) * ↑(num_edges G v u) ≤ if u ∈ S then 0 else -↑(num_edges G v u) := by
        intro u
        by_cases h_u_in_S : u ∈ S
        · simp [h_u_in_S]
          dsimp [S] at h_u_in_S h_v
          rw [h_u_in_S,h_v]
          simp
        · simp [h_u_in_S]
          have ineq := h_lt u h_u_in_S
          rw [← h_v] at ineq
          apply le_of_sub_nonneg
          rw [neg_eq_neg_one_mul, ← sub_mul]
          apply mul_nonneg
          linarith
          exact Nat.cast_nonneg _
      have h_sum : ∑ w : V, (σ w - σ v) * ↑(num_edges G v w) ≤ ∑ w : V, if w ∈ S then 0 else -↑(num_edges G v w) := by
        apply Finset.sum_le_sum
        intro u _
        specialize h_diff_mul u

        exact h_diff_mul
      suffices ∑ u : V, ((σ u - σ v) * ↑(num_edges G v u)) ≤ -↑ (∑ u: V, (flow O u v)) by linarith
      refine le_trans h_sum ?_
      apply le_of_neg_le_neg
      rw [neg_neg, Nat.cast_sum, neg_eq_neg_one_mul, mul_comm (-1), Finset.sum_mul]


      apply sum_le_sum

      intro u _
      by_cases h_u_in_S : u ∈ S
      · -- Case: u ∈ S. No edges from u to v.
        simp only [h_u_in_S]
        rw [if_true]
        contrapose! h_flow
        use u
        norm_num at h_flow
        exact ⟨h_flow, h_u_in_S⟩
      · -- Case : u ∉ S.
        simp [h_u_in_S]
        -- Goal: flow O u v ≤ num_edges G v u
        rw [← opp_flow O v u]
        linarith
    specialize E_eff v
    rw [h_σ] at E_eff
    rw [add_apply] at E_eff
    dsimp [ordiv] at E_eff
    linarith
  -- Now we must find a source of O relative to S
  let S' := Finset.filter (λ v => v ∈ S) Finset.univ
  have S'_nonempty : S'.Nonempty := by
    rcases S_nonempty with ⟨v, h_v_in_S⟩
    use v
    simp [S']
    exact h_v_in_S
  have h := subset_source G O S' S'_nonempty h_acyclic
  rcases h with ⟨v, h_v_in_S', h_flow⟩
  use v
  simp [S'] at h_v_in_S'
  constructor
  · exact h_v_in_S'
  · intro w h_flow_w_v
    specialize h_flow w
    by_contra!
    have : w ∈ S' := by
      simp [S']
      exact this
    apply h_flow at this
    linarith

lemma ordiv_q_reduced {G : CFGraph V} (O : CFOrientation G) {q : V} (h_acyclic : is_acyclic G O) (h_unique_source : ∀ w, is_source G O w → w = q) : q_reduced G q (ordiv G O) := by
  constructor
  · -- Show ordiv is effective away from q
    intro v h_v_ne_q
    simp at h_v_ne_q -- Now just ¬ v = q
    dsimp [ordiv]
    suffices indeg G O v > 0  by
      linarith
    specialize h_unique_source v
    contrapose! h_v_ne_q with indeg_zero
    apply h_unique_source
    apply Nat.eq_zero_of_le_zero at indeg_zero
    dsimp [is_source]
    simp [indeg_zero]
  · -- Show no valid firing move exists for subsets not containing q
    intro S h_q_S S_nonempty
    have h_source := subset_source G O S S_nonempty h_acyclic
    rcases h_source with ⟨v, h_v_S, h_flow⟩
    use v
    refine ⟨h_v_S, ?_⟩
    dsimp [ordiv]
    -- Cancel -1 from both sides
    apply Int.lt_of_le_sub_one
    apply sub_le_sub_right
    -- Expand indeg and compare terms
    rw [indeg_eq_sum_flow O v, Nat.cast_sum]
    -- Split the LHS sum into the x ∈ S part and the x ∉ S part
    have flow_bound (w : V) : flow O w v ≤ if w ∈ S then 0 else num_edges G w v := by
      by_cases h_w_in_S : w ∈ S
      · -- Case: w ∈ S
        simp [h_w_in_S]
        specialize h_flow w
        apply h_flow at h_w_in_S
        dsimp [flow] at h_w_in_S
        -- Now deduce (w,v) ∉ O.directed_edges from count = 0.
        exact  Multiset.count_eq_zero.mp h_w_in_S
      · -- Case: w ∉ S
        simp [h_w_in_S]
        rw [← opp_flow O w v]
        linarith
    have sum_flow_bound : ∑ w : V, ↑(flow O w v) ≤ ∑ w : V, if w ∈ S then 0 else ↑(num_edges G w v) := by
      apply Finset.sum_le_sum
      intro u _
      specialize flow_bound u
      exact flow_bound
    rw [Finset.sum_ite, sum_const,smul_zero, zero_add] at sum_flow_bound
    -- Do some annoying casting business to remove ↑.
    rw [← Nat.cast_sum, ← Nat.cast_sum]
    apply Nat.cast_le.mpr
    apply le_trans sum_flow_bound
    -- Final step: we have num_edges G _ v on LHS and G v _ on the right. Use symemtriy.
    simp [num_edges_symmetric]

/-- The canonical divisor assigns degree - 2 to each vertex.
    This is independent of orientation and equals D(O) + D(reverse(O)) -/
def canonical_divisor (G : CFGraph V) : CFDiv V :=
  λ v => (vertex_degree G v) - 2

/-- Auxillary Lemma: Double canonical difference is identity -/
lemma canonical_double_diff (G : CFGraph V) (D : CFDiv V) :
  (λ v => canonical_divisor G v - (canonical_divisor G v - D v)) = D := by
  funext v; simp

/- Helper: Definition of reversing an orientation -/
def CFOrientation.reverse (G : CFGraph V) (O : CFOrientation G) : CFOrientation G where
  directed_edges := O.directed_edges.map Prod.swap -- Use Prod.swap directly
  count_preserving v w := by
    rw [O.count_preserving v w]

    have h_vw_rev_eq_wv_orig :
        Multiset.count (v,w) (O.directed_edges.map Prod.swap) = Multiset.count (w,v) O.directed_edges := by
      rw [Multiset.count_map (f := Prod.swap)]
      rw [Multiset.count_eq_card_filter_eq] -- Or Multiset.count, Multiset.countP_eq_card_filter
      apply congr_arg Multiset.card
      ext e
      simp only [Multiset.mem_filter, and_congr_left_iff, Prod.ext_iff, Prod.fst_swap, Prod.snd_swap, eq_comm, and_comm]

    have h_wv_rev_eq_vw_orig :
        Multiset.count (w,v) (O.directed_edges.map Prod.swap) = Multiset.count (v,w) O.directed_edges := by
      rw [Multiset.count_map (f := Prod.swap)]
      rw [Multiset.count_eq_card_filter_eq]
      apply congr_arg Multiset.card
      ext e
      simp only [Multiset.mem_filter, and_congr_left_iff, Prod.ext_iff, Prod.fst_swap, Prod.snd_swap, eq_comm, and_comm]

    conv_rhs =>
      congr
      · change Multiset.count (v,w) (O.directed_edges.map Prod.swap)
        rw [h_vw_rev_eq_wv_orig]
      · change Multiset.count (w,v) (O.directed_edges.map Prod.swap)
        rw [h_wv_rev_eq_vw_orig]

    rw [add_comm (Multiset.count (w,v) O.directed_edges)]
  no_bidirectional v w := by -- The `directed_edges` for this proof is O.directed_edges.map Prod.swap
    cases O.no_bidirectional v w with
    | inl h_vw_O_zero => -- Multiset.count (v, w) O.directed_edges = 0
      apply Or.inr
      rw [Multiset.count_eq_zero]
      intro h_wv_mem_rev_contra
      have h_vw_mem_O_derived : (v,w) ∈ O.directed_edges := by
        obtain ⟨p, h_p_mem_O, h_swap_p_eq_wv⟩ := Multiset.mem_map.mp h_wv_mem_rev_contra
        have h_p_is_vw : p = (v,w) := by { apply Prod.ext; exact (Prod.mk.inj h_swap_p_eq_wv).2; exact (Prod.mk.inj h_swap_p_eq_wv).1 }
        rwa [h_p_is_vw] at h_p_mem_O
      exact (Multiset.count_eq_zero.mp h_vw_O_zero) h_vw_mem_O_derived
    | inr h_wv_O_zero => -- Multiset.count (w, v) O.directed_edges = 0
      apply Or.inl
      rw [Multiset.count_eq_zero]
      intro h_vw_mem_rev_contra
      have h_wv_mem_O_derived : (w,v) ∈ O.directed_edges := by
        obtain ⟨p, h_p_mem_O, h_swap_p_eq_vw⟩ := Multiset.mem_map.mp h_vw_mem_rev_contra
        have h_p_is_wv : p = (w,v) := by { apply Prod.ext; exact (Prod.mk.inj h_swap_p_eq_vw).2; exact (Prod.mk.inj h_swap_p_eq_vw).1 }
        rwa [h_p_is_wv] at h_p_mem_O
      exact (Multiset.count_eq_zero.mp h_wv_O_zero) h_wv_mem_O_derived

-- This lemma was added later than the next couple; it may be useful to use it to simplify those proof.
lemma flow_reverse {G : CFGraph V} (O : CFOrientation G) (v w : V) :
  flow (O.reverse G) v w = flow O w v := by
  dsimp [flow, CFOrientation.reverse]
  rw [Multiset.count_map (f := Prod.swap)]
  rw [Multiset.count_eq_card_filter_eq]
  apply congr_arg Multiset.card
  have : ∀ a : (V × V), a = ⟨w,v⟩ ↔ ⟨v,w⟩ = Prod.swap a := by
    intro a
    constructor
    · intro h_eq
      rw [h_eq]
      rfl
    · intro h_eq
      rw [← Prod.swap_swap a]
      rw [← h_eq]
      simp
  apply Multiset.filter_congr
  intro e _
  specialize this e
  -- "this" is now our statement, but with the iff in the opposite order
  rw [← this]
  constructor
  intro h; rw [h]
  intro h; rw [h]

/- Helper: indegree in reversed orientation equals outdegree in original -/
lemma indeg_reverse_eq_outdeg (G : CFGraph V) (O : CFOrientation G) (v : V) :
  indeg G (O.reverse G) v = outdeg G O v := by
  classical
  simp only [indeg, outdeg]
  rw [← Multiset.countP_eq_card_filter, ← Multiset.countP_eq_card_filter]
  let O_rev_edges_def : (CFOrientation.reverse G O).directed_edges = O.directed_edges.map Prod.swap := by rfl
  conv_lhs => rw [O_rev_edges_def]
  rw [Multiset.countP_map]
  simp only [Function.comp_apply, Prod.snd_swap]
  simp only [Multiset.countP_eq_card_filter]

/- Helper: If an orientation is acyclic, its reverse is also acyclic -/
lemma is_acyclic_reverse_of_is_acyclic (G : CFGraph V) (O : CFOrientation G)
    (h_acyclic : is_acyclic G O) :
  is_acyclic G (O.reverse G) := by
  intro p
  let q : DirectedPath O := {
    vertices := p.vertices.reverse,
    non_empty := by
      rw [List.length_reverse p.vertices]
      exact p.non_empty,
    valid_edges := by
      have p_valid := p.valid_edges
      have hyp := List.chain'_reverse.mpr p_valid
      have repl: (directed_edge G O) = (λ a b => (b,a) ∈ (CFOrientation.reverse G O).directed_edges) := by
        funext a b
        simp
        constructor
        -- Forward direction
        intro h_a_b
        dsimp [CFOrientation.reverse]
        simp
        use a, b
        exact ⟨h_a_b, rfl, rfl⟩
        -- Backward direction
        intro h_b_a_rev
        dsimp [CFOrientation.reverse] at h_b_a_rev
        simp at h_b_a_rev
        rcases h_b_a_rev with ⟨a1,b1, h⟩
        obtain ⟨h_ba_in_O, swap_b, swap_a⟩ := h
        rw [← swap_a, ← swap_b]
        exact h_ba_in_O
      rw [← repl] at hyp
      exact hyp
  }
  have h_non_repeating_q : non_repeating q := h_acyclic q
  exact List.nodup_reverse.mp h_non_repeating_q


lemma divisor_reverse_orientation {G : CFGraph V} (O : CFOrientation G)  : ordiv G O + ordiv G (O.reverse) = canonical_divisor G := by
  let O' := O.reverse
  funext v
  rw [add_apply]
  dsimp [ordiv, canonical_divisor]
  suffices indeg G O v + indeg G O' v = vertex_degree G v by
    dsimp [vertex_degree] at this
    rw [← this]
    ring
  rw [indeg_eq_sum_flow, indeg_eq_sum_flow, Nat.cast_sum, Nat.cast_sum]
  dsimp [vertex_degree]
  rw [← sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  rw [← opp_flow O v w]
  rw [Nat.cast_add, add_comm]
  simp
  -- Goal is now: flow O' w v = flow O v w
  rw [flow_reverse O w v]

/-- Create a multiset with a given count function. This seems
  likely to be in Mathlib already, but I didn't find it. -/
def multiset_of_count {T : Type*} [Fintype T] (f : T → ℕ) : Multiset T :=
  (univ : Finset T).val.bind (fun e => Multiset.replicate (f e) e)

@[simp] lemma count_of_multiset_of_count (f : V × V → ℕ) : ∀ e : V × V, Multiset.count e (multiset_of_count f) = f e := by
  intro e
  dsimp [multiset_of_count]
  rw [Multiset.count_bind]
  simp [Multiset.count_replicate]

def orientation_from_flow {G : CFGraph V} (f : V × V → ℕ) (h_count_preserving : ∀ v w : V, f (v,w) + f (w,v) = num_edges G v w)
    (h_no_bidirectional : ∀ v w : V, f (v,w) = 0 ∨ f (w,v) = 0) : CFOrientation G :=
  {
    directed_edges := multiset_of_count f,
    count_preserving := by
      intro v w
      simp
      rw [h_count_preserving v w]
    ,
    no_bidirectional := by
      intro v w
      simp
      exact h_no_bidirectional v w
  }

def burn_orientation {G : CFGraph V} {q : V} {c : Config V q} (L : burn_list G c) (h_full : ∀ (v :V), v ∈ L.list): CFOrientation G := orientation_from_flow (burn_flow L) (burn_flow_reverse L h_full) (burn_flow_directed L h_full)

/-- Utility for proving acyclicity. This is a fairly basic fact
  that may be in Mathlib, but I haven't found it. -/
lemma nodup_of_map_nodup (S T : Type*) (L : List S) (f : S → T) :  (L.map f).Nodup → L.Nodup := by
  intro h_nodup
  cases h : L with
  | nil =>
    simp
  | cons x xs =>
    rw [h] at h_nodup
    simp at h_nodup
    simp
    constructor
    · -- First element does not repeat
      have h' := h_nodup.1
      contrapose! h'
      have h_in_map : f x ∈ (xs.map f) := by
        rw [List.mem_map]
        use x
      use x
    · -- Rest of list is nodup
      have h' := h_nodup.2
      -- Recursive call. Lean knows that this terminates.
      exact nodup_of_map_nodup S T xs f h'

-- Some basic facts about decreasing sequences.
-- Again, these may be in Mathlib somewhere, but
-- I haven't found them.

def dec (L : List ℕ) : Prop :=
    match L with
    | [] => True
    | x :: xs => (∀ y ∈ xs, x > y) ∧ dec xs

lemma nodup_of_dec (L : List ℕ) (h_dec : dec L) : L.Nodup := by
  cases h : L with
  | nil =>
    simp
  | cons x xs =>
    rw [h] at h_dec
    simp
    constructor
    · -- First element does not repeat
      have h' := h_dec.1
      intro h_in_xs
      specialize h' x h_in_xs
      linarith
    · -- Rest of list is nodup
      have h' := h_dec.2
      -- Recursive call. Lean knows that this terminates.
      exact nodup_of_dec xs h'

def dec' (L : List ℕ) : Prop :=
  match L with
  | [] => True
  | [x] => True
  | x :: y :: zs => (x > y) ∧ dec' (y :: zs)

lemma dec_iff_dec' (L : List ℕ) : dec L ↔ dec' L := by
  cases h : L with
  | nil =>
    simp [dec, dec']
  | cons x xs =>
    cases h' : xs with
    | nil =>
      simp [dec, dec']
    | cons y ys =>
      constructor
      . -- dec → dec'
        intro h_dec
        simp [dec']
        constructor
        · exact h_dec.1 y (by simp)
        · exact (dec_iff_dec' (y::ys)).mp h_dec.2
      . -- dec' → dec
        intro h_dec'
        simp [dec]
        simp [dec'] at h_dec'
        constructor
        · constructor
          exact h_dec'.1
          have := (dec_iff_dec' (y::ys)).mpr h_dec'.2
          dsimp [dec] at this
          have := this.1
          intro z h_z_in_ys
          specialize this z
          apply this at h_z_in_ys
          linarith [h_dec'.1]
        · exact (dec_iff_dec' (y::ys)).mpr h_dec'.2


-- This proof is a tangled mess. It can probably be simplified.
lemma dp_dec {G : CFGraph V} {q : V} {c : Config V q} (L : burn_list G c) (h_full : ∀ (v :V), v ∈ L.list) (p : DirectedPath (burn_orientation L h_full)) :
  dec (p.vertices.map (λ v => L.list.indexOf v)) := by
  suffices h_dec' : dec' (p.vertices.map (λ v => L.list.indexOf v)) by
    rw [← dec_iff_dec'] at h_dec'
    exact h_dec'
  cases h : p.vertices with
  | nil =>
    simp [dec']
  | cons v vs =>
    cases h' : vs with
    | nil =>
      simp [dec']
    | cons v' vs' =>
      rw [h'] at h
      simp [dec']
      have h_valid := p.valid_edges
      rw [h] at h_valid
      simp at h_valid
      have h_dec := h_valid.1
      dsimp [directed_edge] at h_dec
      simp [burn_orientation] at h_dec
      dsimp [orientation_from_flow] at h_dec
      have h_edge: Multiset.count ⟨v,v'⟩ (multiset_of_count (burn_flow L)) > 0 := by
        contrapose! h_dec with h_count
        apply Nat.eq_zero_of_le_zero at h_count
        exact Multiset.count_eq_zero.mp h_count
      simp at h_edge
      dsimp [burn_flow] at h_edge

      constructor
      · -- Show first element greater than second
        by_contra! h_not_gt
        have : ¬ ( v ∈ L.list ∧ List.indexOf v' L.list < List.indexOf v L.list) := by
          simp [h_not_gt]
        simp [this] at h_edge
      · -- Show rest is decreasing
        let p' : DirectedPath (burn_orientation L h_full) := {
          vertices := v' :: vs',
          non_empty := by
            rw [List.length_cons]
            exact Nat.succ_pos _,
          valid_edges := by
            have := p.valid_edges
            rw [h] at this
            simp at this
            exact this.2
        }
        have goal := dp_dec L h_full p'
        rw [dec_iff_dec'] at goal
        have : p'.vertices = v' :: vs' := by
          rfl
        rw [this] at goal
        exact goal
termination_by p.vertices.length
decreasing_by
  rw [h'] at h
  rw [h]
  simp

lemma burn_nodup {G : CFGraph V} {q : V} {c : Config V q} (L : burn_list G c) (h_full : ∀ (v :V), v ∈ L.list) (p : DirectedPath (burn_orientation L h_full)) : p.vertices.Nodup := by
  let q : List ℕ := p.vertices.map (λ v => L.list.indexOf v)
  suffices q.Nodup by
    exact nodup_of_map_nodup _ _ p.vertices (λ v => L.list.indexOf v) this
  -- Now prove that q is nodup
  have h_dec := dp_dec L h_full p
  exact nodup_of_dec q h_dec

lemma burn_acyclic {G : CFGraph V} {q : V} {c : Config V q} (L : burn_list G c) (h_full : ∀ (v :V), v ∈ L.list) :
  is_acyclic G (burn_orientation L h_full) := by
  dsimp [is_acyclic]
  intro p
  dsimp [non_repeating]
  exact burn_nodup L h_full p

lemma burn_unique_source {G : CFGraph V} {q : V} {c : Config V q} (L : burn_list G c) (h_full : ∀ (v :V), v ∈ L.list) :
  ∀ w, is_source G (burn_orientation L h_full) w → w = q := by
  intro w h_source
  dsimp [is_source] at h_source
  rw [indeg_eq_sum_flow (burn_orientation L h_full) w] at h_source
  dsimp [burn_orientation,flow,orientation_from_flow] at h_source
  simp only [count_of_multiset_of_count] at h_source
  -- Remove the decide and true parts
  contrapose! h_source with h_ne
  have ineq := burnin_degree L w (h_full w) h_ne
  -- rw [Nat.cast_sum] at ineq
  have : c.vertex_degree w ≥ 0 := by
    apply c.non_negative w
  let ineq := lt_of_le_of_lt this ineq
  apply ne_of_lt at ineq
  contrapose! ineq
  rw [Nat.cast_sum]
  simp at ineq
  simp [ineq]

/-- Theorem: Dhar's burning algorithm produces, from a superstable configuration, an orientation giving a maximal superstable above it. -/
theorem superstable_dhar {G : CFGraph V} {q : V} {c : Config V q} (h_ss : superstable G q c) : ∃ (O : CFOrientation G) (h_acyc: is_acyclic G O) (h_unique_source : ∀ w, is_source G O w → w = q), config_ge (orientation_to_config G O q h_acyc h_unique_source) c := by
  rcases superstable_burn_list G c h_ss with ⟨L, h_full⟩
  let O := burn_orientation L h_full
  have h_acyc := burn_acyclic L h_full
  have h_unique_source := burn_unique_source L h_full
  use O, h_acyc, h_unique_source
  intro v
  dsimp [orientation_to_config, config_of_source]
  by_cases h_vq : v = q
  · -- Case: v = q
    rw [h_vq]
    simp
    linarith [c.q_zero]
  · -- Case: v ≠ q
    simp [h_vq]
    rw [indeg_eq_sum_flow O v]
    dsimp [flow]
    dsimp [O, burn_orientation, orientation_from_flow]
    simp only [count_of_multiset_of_count]
    have ineq := burnin_degree L v (h_full v) h_vq
    linarith
