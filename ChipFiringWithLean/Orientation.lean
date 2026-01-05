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
structure CFOrientation (G : CFGraph V) where
  /-- The set of directed edges in the orientation -/
  directed_edges : Multiset (V × V)
  /-- Preserves edge counts between vertex pairs -/
  count_preserving : ∀ v w,
    num_edges G v w =
    Multiset.count (v, w) directed_edges + Multiset.count (w, v) directed_edges
  /-- No bidirectional edges in the orientation -/
  no_bidirectional : ∀ v w,
    Multiset.count (v, w) directed_edges = 0 ∨
    Multiset.count (w, v) directed_edges = 0

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
        exact G.loopless v
      · -- case: e ≠ ⟨u,v⟩
        by_cases h_e' : e = ⟨v,u⟩
        · -- case: e = ⟨v,u⟩
          simp [h_e']
          intro h_eq _
          rw [h_eq]
          exact G.loopless u
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
def is_source (G : CFGraph V) (O : CFOrientation G) (v : V) : Prop :=
  indeg G O v = 0

/-- A vertex is a sink if it has no outgoing edges (outdegree = 0) -/
def is_sink (G : CFGraph V) (O : CFOrientation G) (v : V) : Prop :=
  outdeg G O v = 0

def directed_edge (G : CFGraph V) (O : CFOrientation G) (u v : V) : Prop :=
  (u, v) ∈ O.directed_edges

/-- Helper function for safe list access -/
def list_get_safe {α : Type} (l : List α) (i : Nat) : Option α :=
  if h: i < l.length then some (l.get ⟨i, h⟩) else none

/-- A directed path in a graph under an orientation -/
structure DirectedPath {G : CFGraph V} (O : CFOrientation G) where
  /-- The sequence of vertices in the path -/
  vertices : List V
  /-- Path must not be empty (at least one vertex) -/
  non_empty : vertices.length > 0
  /-- Every consecutive pair forms a directed edge -/
  valid_edges : List.IsChain (directed_edge G O) vertices

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
  let R : V → V → Prop := fun a b => directed_edge G O a b
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
  exact h_not_source h_eq_zero

/-- For vertices that are not sources, indegree - 1 is non-negative. -/
lemma indeg_minus_one_nonneg_of_not_source (G : CFGraph V) (O : CFOrientation G) (v : V) :
    ¬ is_source G O v → 0 ≤ (indeg G O v : ℤ) - 1 := by
  intro h_not_source
  have h_indeg_ge_1 : indeg G O v ≥ 1 := indeg_ge_one_of_not_source G O v h_not_source
  apply Int.sub_nonneg_of_le
  exact Nat.cast_le.mpr h_indeg_ge_1


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
        valid_edges := List.isChain_singleton v
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
            dsimp [new_path, List.IsChain]
            cases h_case : p.vertices with
            | nil =>
              -- Path was just [v], so new path is [u, v]
              simp
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
              simp
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
lemma acyclic_has_source (G : CFGraph V) (O : CFOrientation G) :
  is_acyclic G O → ∃ v : V, is_source G O v := by
  intro h_acyclic
  have h := subset_source G O Finset.univ Finset.univ_nonempty h_acyclic
  rcases h with ⟨v, _, h_source⟩
  use v
  dsimp [is_source]
  rw [indeg_eq_sum_flow]
  apply Finset.sum_eq_zero
  exact h_source

lemma is_source_of_unique_source {G : CFGraph V} (O : CFOrientation G) {q : V} (h_acyclic : is_acyclic G O)
    (h_unique_source : ∀ w, is_source G O w → w = q) :
  is_source G O q := by
  rcases acyclic_has_source G O h_acyclic with ⟨q', h_q'⟩
  specialize h_unique_source q'
  have := h_unique_source h_q'
  rw [this] at h_q'
  exact h_q'


/-- Configuration associated with a source vertex q under orientation O.
    Requires O to be acyclic and q to be the unique source.
    For each vertex v ≠ q, assigns indegree(v) - 1 chips. Assumes q is the unique source. -/
def config_of_source {G : CFGraph V} {O : CFOrientation G} {q : V}
    (h_acyclic : is_acyclic G O) (h_unique_source : ∀ w, is_source G O w → w = q) : Config V q :=
  { vertex_degree := λ v => if v = q then 0 else (indeg G O v : ℤ) - 1,
    q_zero := by simp
    non_negative := by
      intro v
      simp
      split_ifs with h_eq
      · linarith
      · have h_not_source : ¬ is_source G O v := by
          intro hs_v
          exact h_eq (h_unique_source v hs_v)
        exact indeg_minus_one_nonneg_of_not_source G O v h_not_source
  }

/-
## Orientation divisors and their properties
-/

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

/-- Lemma: CFOrientation to config preserves indegrees -/
lemma orientation_to_config_indeg (G : CFGraph V) (O : CFOrientation G) (q : V)
    (h_acyclic : is_acyclic G O) (h_unique_source : ∀ w, is_source G O w → w = q) (v : V) :
    (orientation_to_config G O q h_acyclic h_unique_source).vertex_degree v =
    if v = q then 0 else (indeg G O v : ℤ) - 1 := by
  -- This follows directly from the definition of config_of_source
  simp only [orientation_to_config] at *
  -- Use the definition of config_of_source
  exact rfl



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




  /-- Lemma: Given a list of disjoint vertex sets that form a partition of V,
    an acyclic orientation is uniquely determined by this partition where
    each set contains vertices with same indegree. -/
lemma orientation_determined_by_indegrees {G : CFGraph V}
  (O O' : CFOrientation G) :
  is_acyclic G O → is_acyclic G O' →
  (∀ v : V, indeg G O v = indeg G O' v) →
  O = O' := by
  intro h_acyc h_acyc' h_indeg_eq

  let S := { e : V × V | O.directed_edges.count e > O'.directed_edges.count e }
  have suff_S_empty : S = ∅ → O = O' := by
    intro h_S_empty
    have h_ineq (u v : V) : flow O u v ≤ flow O' u v := by
      have h_nin: ⟨u,v⟩ ∉ S := by
        rw [h_S_empty]
        simp
      dsimp [S] at h_nin
      linarith
    simp [eq_orient O O']
    intro u v
    by_contra h_neq
    have h_uv_le := h_ineq u v
    have h_lt : flow O u v < flow O' u v := lt_of_le_of_ne h_uv_le h_neq
    have h_indeg_contra : indeg G O v < indeg G O' v := by
      rw [indeg_eq_sum_flow O v, indeg_eq_sum_flow O' v]
      apply Finset.sum_lt_sum
      intro x hx
      exact h_ineq x v
      use u
      simp [h_lt]
    linarith [h_indeg_eq v]
  apply suff_S_empty

  -- A small helper we'll need a couple time later
  have directed_edge_of_S (e : V × V) : e ∈ S → directed_edge G O e.1 e.2 :=  by
    dsimp [directed_edge]
    intro h
    dsimp [S] at h
    have h_pos_count : count e O.directed_edges > 0 := by
      omega
    apply Multiset.count_pos.mp
    exact h_pos_count

  -- We now must show that S is empty.
  -- Do so buy showing any element in S belongs to an infinite directd path
  have going_up : ∀ e ∈ S, ∃ f ∈ S, f.2 = e.1 := by
    intro e h_e_in_S
    obtain ⟨u,v⟩ := e
    by_contra! h_no_parent
    have all_flow_le : ∀ (w : V) , flow O w u ≤ flow O' w u := by
      intro w
      by_contra h_flow_gt
      apply lt_of_not_ge at h_flow_gt
      specialize h_no_parent ⟨w,u⟩
      simp at h_no_parent
      exact h_no_parent h_flow_gt
    have one_flow_lt : ∃ (w : V), flow O w u < flow O' w u := by
      contrapose! h_e_in_S
      dsimp [S]
      suffices flow O u v ≤ flow O' u v by linarith
      specialize h_e_in_S v
      by_contra flow_lt
      apply lt_of_not_ge at flow_lt
      have edges_lt := add_lt_add_of_le_of_lt h_e_in_S flow_lt
      rw [opp_flow O v u, opp_flow O' v u] at edges_lt
      linarith

    have h: ∑ (w : V), flow O w u < ∑ (w : V), flow O' w u := by
      apply Finset.sum_lt_sum
      intro i _
      exact all_flow_le i
      rcases one_flow_lt with ⟨w, h_flow_lt⟩
      use w
      constructor
      simp
      exact h_flow_lt

    repeat rw [← indeg_eq_sum_flow] at h
    specialize h_indeg_eq u
    linarith

  -- For contradiction, we can build an infinite directed path in G under O
  by_contra! h_S_nonempty
  rcases h_S_nonempty with ⟨e_start, h_e_start_in_S⟩
  have S_path (n : ℕ) : ∃ (p : DirectedPath O), p.vertices.length = n + 2 ∧ List.IsChain (λ ( u v : V) => ⟨u,v⟩ ∈ S) p.vertices := by
    induction' n with n ih
    . -- Base case: n = 0, i.e. length 2 path
      use {
        vertices := [e_start.1, e_start.2],
        non_empty := by simp,
        valid_edges := by
          simp [List.isChain_cons]
          exact directed_edge_of_S e_start h_e_start_in_S
      }
      simp [h_e_start_in_S]
    . -- Inductive step
      rcases ih with ⟨p0, h_len, h_chain⟩
      -- Write p0 as v :: w :: rest, using the fact that its length is at least 2
      have : ∃ (v w : V) (rest : List V), p0.vertices = v :: w :: rest := by
        cases h_p0 : p0.vertices with
        | nil =>
          -- This case should not happen since p0.vertices has length n + 2 ≥ 2
          exfalso
          rw [h_p0] at h_len
          simp at h_len
        | cons v ws =>
          cases h_ws : ws with
          | nil =>
            -- This case should not happen since p0.vertices has length n + 2 ≥ 2
            exfalso
            rw [h_p0,h_ws] at h_len
            simp at h_len
          | cons w rest =>
            use v, w, rest
      rcases this with ⟨v, w, rest, h_p0_eq⟩
      -- Now, p0.vertices = v :: w :: rest
      specialize going_up ⟨v,w⟩
      have h_vw_in_S : ⟨v,w⟩ ∈ S := by
        -- From h_chain, we know that ⟨v,w⟩ ∈ S
        rw [h_p0_eq] at h_chain
        simp [List.isChain_cons] at h_chain
        exact h_chain.left
      specialize going_up h_vw_in_S
      rcases going_up with ⟨f, h_f_in_S, h_f_to_v⟩
      let new_path_list : List V := f.1 :: p0.vertices
      use {
        vertices := new_path_list,
        non_empty := by
          rw [List.length_cons]
          exact Nat.succ_pos _,
        valid_edges := by
          dsimp [new_path_list]
          -- Check that the first edge is valid
          rw [h_p0_eq]
          simp [List.isChain_cons]
          constructor
          have : f.2 = v := h_f_to_v
          rw [← this]
          exact directed_edge_of_S f h_f_in_S
          -- The rest of the path is valid from induction
          have h_ind := p0.valid_edges
          rw [h_p0_eq] at h_ind
          simp [List.isChain_cons] at h_ind
          exact h_ind
        }
      -- Now must verify that this new path has the right length
      constructor
      rw [List.length_cons]
      rw [h_len]
      -- Verify the chain property
      dsimp [new_path_list]
      simp [List.isChain_cons, h_p0_eq]
      -- Verify the first link is in S
      constructor
      have : f.2 = v := h_f_to_v
      rw [← this]
      exact h_f_in_S
      -- The rest of the chain follows from h_chain
      have h_ind := h_chain
      simp only [h_p0_eq] at h_ind
      simp [List.isChain_cons] at h_ind
      exact h_ind
  specialize S_path (Fintype.card V)
  rcases S_path with ⟨p, h_len, _⟩
  linarith  [path_length_bound p (h_acyc p)]

/-- Lemma proving uniqueness of orientations giving same config -/
theorem helper_config_to_orientation_unique (G : CFGraph V) (q : V)
    (c : Config V q)
    (h_super : superstable G q c)
    (h_max : maximal_superstable G c)
    (O₁ O₂ : CFOrientation G)
    (h_acyc₁ : is_acyclic G O₁)
    (h_acyc₂ : is_acyclic G O₂)
    (h_src₁ : is_source G O₁ q)
    (h_src₂ : is_source G O₂ q)
    (h_unique_source₁ : ∀ w, is_source G O₁ w → w = q)
    (h_unique_source₂ : ∀ w, is_source G O₂ w → w = q)
    (h_eq₁ : orientation_to_config G O₁ q h_acyc₁ h_unique_source₁ = c)
    (h_eq₂ : orientation_to_config G O₂ q h_acyc₂ h_unique_source₂ = c) :
    O₁ = O₂ := by
  apply orientation_determined_by_indegrees O₁ O₂ h_acyc₁ h_acyc₂
  intro v

  have h_deg₁ := orientation_to_config_indeg G O₁ q h_acyc₁ h_unique_source₁ v
  have h_deg₂ := orientation_to_config_indeg G O₂ q h_acyc₂ h_unique_source₂ v

  have h_config_eq : (orientation_to_config G O₁ q h_acyc₁ h_unique_source₁).vertex_degree v =
                     (orientation_to_config G O₂ q h_acyc₂ h_unique_source₂).vertex_degree v := by
    rw [h_eq₁, h_eq₂]

  by_cases hv : v = q
  · -- Case v = q: Both vertices are sources, so indegree is 0
    rw [hv]
    -- Use the explicit source assumptions h_src₁ and h_src₂
    rw [h_src₁, h_src₂]
  · -- Case v ≠ q: use vertex degree equality
    rw [h_deg₁, h_deg₂] at h_config_eq
    simp only [if_neg hv] at h_config_eq
    -- From config degrees being equal, show indegrees are equal
    have h := congr_arg (fun x => x + 1) h_config_eq
    simp only [sub_add_cancel] at h
    -- Use nat cast injection
    exact (Nat.cast_inj.mp h)

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
  exact h_q_source

lemma ordiv_unwinnable (G : CFGraph V) (O : CFOrientation G) :
  is_acyclic G O → ¬ winnable G (ordiv G O) := by
  intro h_acyclic
  by_contra h_win
  let D := ordiv G O
  rcases h_win with ⟨E, E_eff, E_equiv⟩
  dsimp [Eff] at E_eff
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
    simp [S] at h_u
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

lemma helper_orientation_config_superstable (G : CFGraph V) (O : CFOrientation G) (q : V)
    (h_acyc : is_acyclic G O) (h_unique_source : ∀ w, is_source G O w → w = q) :
    superstable G q (orientation_to_config G O q h_acyc h_unique_source) := by
    let c := orientation_to_config G O q h_acyc h_unique_source
    apply (superstable_iff_q_reduced G q (genus G -1) c).mpr

    have h_c := config_and_divisor_from_O O h_acyc h_unique_source
    dsimp [c]
    rw [h_c]
    have : genus G - 1 = deg ((orqed O h_acyc h_unique_source).D) := by
      dsimp [orqed]
      rw [degree_ordiv O]
    rw [this]
    rw [div_of_config_of_div (orqed O h_acyc h_unique_source)]
    dsimp [orqed]
    exact ordiv_q_reduced O h_acyc h_unique_source



/-
## Reverse orientations and the link to the canonical divisor.
This discussion requires the *handshakeing lemma* along the way, to compute the degree of the canonical divisor.
-/

/-- The canonical divisor assigns degree - 2 to each vertex.
    This is independent of orientation and equals D(O) + D(reverse(O)) -/
def canonical_divisor (G : CFGraph V) : CFDiv V :=
  λ v => (vertex_degree G v) - 2

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
      simp only [Prod.ext_iff, Prod.fst_swap, Prod.snd_swap, eq_comm, and_comm]

    have h_wv_rev_eq_vw_orig :
        Multiset.count (w,v) (O.directed_edges.map Prod.swap) = Multiset.count (v,w) O.directed_edges := by
      rw [Multiset.count_map (f := Prod.swap)]
      rw [Multiset.count_eq_card_filter_eq]
      apply congr_arg Multiset.card
      ext e
      simp only [Prod.ext_iff, Prod.fst_swap, Prod.snd_swap, eq_comm, and_comm]

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

-- This lemma was added later than the next couple; it may be useful to use it to simplify those proofs.
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
  simp only [Prod.snd_swap]
  simp only [Multiset.countP_eq_card_filter]

/- Helper: If an orientation is acyclic, its reverse is also acyclic -/
lemma is_acyclic_reverse_of_is_acyclic (G : CFGraph V) (O : CFOrientation G)
    (h_acyclic : is_acyclic G O) :
  is_acyclic G (O.reverse G) := by
  intro p
  let q : DirectedPath O := {
    vertices := p.vertices.reverse,
    non_empty := by
      rw [List.length_reverse]
      exact p.non_empty,
    valid_edges := by
      have p_valid := p.valid_edges
      have hyp := List.isChain_reverse.mpr p_valid
      -- hyp : List.IsChain (flip (directed_edge G (CFOrientation.reverse G O))) p.vertices
      -- Need to show: List.IsChain (directed_edge G (CFOrientation.reverse G O)) p.vertices.reverse
      -- Since isChain_reverse gives us the flipped relation, we need to show
      -- flip (directed_edge G (CFOrientation.reverse G O)) = directed_edge G O
      convert hyp using 2
      ext a
      simp [directed_edge, CFOrientation.reverse, Multiset.mem_map]
  }
  have h_non_repeating_q : non_repeating q := h_acyclic q
  exact List.nodup_reverse.mp h_non_repeating_q


lemma divisor_reverse_orientation {G : CFGraph V} (O : CFOrientation G)  : ordiv G O + ordiv G (O.reverse) = canonical_divisor G := by
  let O' := O.reverse
  funext v
  rw [add_apply]
  dsimp [ordiv, canonical_divisor]
  suffices indeg G O v + indeg G O' v = vertex_degree G v by
    dsimp [vertex_degree] at this ⊢
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

/-- Helper lemma: In a loopless graph, each edge has distinct endpoints -/
lemma edge_endpoints_distinct (G : CFGraph V) (e : V × V) (he : e ∈ G.edges) :
    e.1 ≠ e.2 := by
  by_contra eq_endpoints
  rcases e with ⟨u,v⟩
  have : u = v := eq_endpoints
  rw [this] at he
  exact G.loopless v he

/-- Helper lemma: Each edge is incident to exactly two vertices -/
lemma edge_incident_vertices_count (G : CFGraph V) (e : V × V) (he : e ∈ G.edges) :
    (Finset.univ.filter (λ v => e.1 = v ∨ e.2 = v)).card = 2 := by
  rw [Finset.card_eq_two]
  exists e.1
  exists e.2
  constructor
  · exact edge_endpoints_distinct G e he
  · ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_insert, Finset.mem_singleton]
    -- The proof here can be simplified using Iff.intro and cases
    apply Iff.intro
    · intro h_mem_filter -- Goal: v ∈ {e.1, e.2}
      cases h_mem_filter with
      | inl h => exact Or.inl (Eq.symm h)
      | inr h => exact Or.inr (Eq.symm h)
    · intro h_mem_set -- Goal: e.1 = v ∨ e.2 = v
      cases h_mem_set with
      | inl h => exact Or.inl (Eq.symm h)
      | inr h => exact Or.inr (Eq.symm h)


/-- Helper lemma: Summing mapped incidence counts equals summing constant 2 (Nat version). -/
lemma map_inc_eq_map_two_nat (G : CFGraph V) :
  Multiset.sum (G.edges.map (λ e => (Finset.univ.filter (λ v => e.1 = v ∨ e.2 = v)).card))
    = 2 * (Multiset.card G.edges) := by
  -- Define the function being mapped
  let f : V × V → ℕ := λ e => (Finset.univ.filter (λ v => e.1 = v ∨ e.2 = v)).card
  -- Define the constant function 2
  let g (_ : V × V) : ℕ := 2
  -- Show f equals g for all edges in G.edges
  have h_congr : ∀ e ∈ G.edges, f e = g e := by
    intro e he
    simp [f, g]
    exact edge_incident_vertices_count G e he
  -- Apply congruence to the map function itself first using map_congr with rfl
  rw [Multiset.map_congr rfl h_congr] -- Use map_congr with rfl
  -- Apply rewrites step-by-step
  rw [Multiset.map_const', Multiset.sum_replicate, Nat.nsmul_eq_mul, Nat.mul_comm]

/-- Helper lemma to rewrite (in-)degree in terms of edge counts from each direction.
This proof is quite clunky, and I suspect it can be simplified. -/
lemma degree_eq_total_flow : ∀ (S : Multiset (V × V)) (v : V), (∀ e ∈ S, e.1 ≠ e.2) →
  ∑ u : V, Multiset.card (Multiset.filter (fun e ↦ e = (v, u) ∨ e = (u, v)) S) = Multiset.card (S.filter (λ e => e.fst = v ∨ e.snd = v)) := by
  -- Induct on the multiset S
  intro S v h_loopless
  induction S using Multiset.induction_on with
  | empty =>
    simp only [Multiset.filter_zero, Multiset.card_zero, Finset.sum_const_zero]
  | cons e_head s_tail ih_s_tail =>
    -- Rewrite both sides using the head and tail
    simp only [Multiset.filter_cons, Multiset.card_add, sum_add_distrib]
    rw [ih_s_tail]
    -- Cancel the like terms in a + b = a + c
    suffices h : ∑ x : V, Multiset.card (if e_head = (v, x) ∨ e_head = (x, v) then {e_head} else 0) = Multiset.card (if e_head.1 = v ∨ e_head.2 = v then {e_head} else 0) by linarith

    by_cases h_head : (e_head.fst = v ∨ e_head.snd = v)
    · -- Case: e_head is incident to v
      simp only [if_pos h_head, Multiset.card_singleton]
      obtain ⟨e,f⟩ := e_head
      rcases h_head with h_left  | h_right
      -- Subcase: e = v
      have e_eq_v : e =v  := h_left
      have f_neq_v : f ≠ v := by
        contrapose! h_left
        simp
        rw [← h_left]
        exact h_loopless ⟨e,f⟩ (by simp)
      simp [e_eq_v, f_neq_v]
      -- Now only one term in this sum is nonzero
      have h (x:V): Multiset.card (if f = x then {(v, f)} else 0) = (if x = f then 1 else 0) := by
        by_cases h_x : x = f
        · simp [h_x]
        · simp [h_x]
          contrapose! h_x
          rw [h_x]
      simp [h]
      -- Subcase: f = v
      -- Similar argument
      have f_eq_v : f = v := h_right
      have e_neq_v : e ≠ v := by
        contrapose! h_right
        simp
        rw [← h_right]
        have := h_loopless ⟨e,f⟩ (by simp)
        intro h_bad
        rw [h_bad] at this
        apply absurd this
        simp

      simp [f_eq_v, e_neq_v]
      -- Now only one term in this sum is nonzero
      have h (x:V): Multiset.card (if e = x then {(e,v)} else 0) = (if x = e then 1 else 0) := by
        by_cases h_x : x = e
        · simp [h_x]
        · simp [h_x]
          contrapose! h_x
          rw [h_x]
      simp [h]
    · -- Case: e_head is not incident to v
      simp only [if_neg h_head]
      apply Finset.sum_eq_zero
      intro x _
      simp
      push_neg at h_head
      contrapose! h_head
      intro h'
      have h'': e_head ≠ ⟨v,x⟩ := by
        contrapose! h'
        simp [h']
      apply h_head at h''
      simp [h'']
    intro e
    specialize h_loopless e
    intro h_tail
    apply h_loopless
    simp [h_tail]

-- Key lemma for handshaking theorem: Sum of edge counts equals incident edge count
lemma sum_num_edges_eq_filter_count (G : CFGraph V) (v : V) :
  ∑ u, num_edges G v u = Multiset.card (G.edges.filter (λ e => e.fst = v ∨ e.snd = v)) := by
  dsimp [num_edges]
  have h_loopless: ∀ e ∈ G.edges, e.1 ≠ e.2 := by
    intro e he
    exact edge_endpoints_distinct G e he
  exact degree_eq_total_flow G.edges v (h_loopless)

/--
**Handshaking Theorem:** In a loopless multigraph \(G\),
the sum of the degrees of all vertices is twice the number of edges:

\[
  \sum_{v \in V} \deg(v) = 2 \cdot \#(\text{edges of }G).
\]
-/
theorem helper_sum_vertex_degrees (G : CFGraph V) :
    ∑ v, vertex_degree G v = 2 * ↑(Multiset.card G.edges) := by
  -- The proof follows from the existing helper lemmas
  calc ∑ v, vertex_degree G v
    = ∑ v, ∑ u, (num_edges G v u : ℤ) := by simp_rw [vertex_degree]
    _ = ∑ v, ↑(∑ u, num_edges G v u) := by simp_rw [← Nat.cast_sum]
    _ = ∑ v, ↑(Multiset.card (G.edges.filter (λ e => e.fst = v ∨ e.snd = v))) := by simp_rw [sum_num_edges_eq_filter_count G]
    _ = ↑(∑ v, Multiset.card (G.edges.filter (λ e => e.fst = v ∨ e.snd = v))) := by rw [← Nat.cast_sum]
    _ = ↑(Multiset.sum (G.edges.map (λ e => (Finset.univ.filter (λ v => e.1 = v ∨ e.2 = v)).card))) := by rw [sum_filter_eq_map G (G.edges) (λ v e => e.fst = v ∨ e.snd = v)]
    _ = ↑(2 * Multiset.card G.edges) := by rw [map_inc_eq_map_two_nat G]
    _ = 2 * ↑(Multiset.card G.edges) := by rw [Nat.cast_mul, Nat.cast_two]

-- Corollary 4.2.3: Degree of canonical divisor equals 2g - 2
theorem degree_of_canonical_divisor (G : CFGraph V) :
    deg (canonical_divisor G) = 2 * genus G - 2 := by
  -- Use sum_sub_distrib to split the sum
  have h1 : ∑ v, (canonical_divisor G v) =
            ∑ v, vertex_degree G v - 2 * Fintype.card V := by
    unfold canonical_divisor
    rw [sum_sub_distrib]
    simp [sum_const]
    ring
  dsimp [deg]
  rw [h1]

  -- Use the fact that sum of vertex degrees = 2|E|
  have h2 : ∑ v, vertex_degree G v = 2 * Multiset.card G.edges := by
    exact helper_sum_vertex_degrees G
  rw [h2]

  -- Use genus definition: g = |E| - |V| + 1
  rw [genus]

  ring

/-
## Creating orientations from burn orders. Building blocks towards Dhar's algorithm.
-/

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
  dec (p.vertices.map (λ v => List.idxOf v L.list)) := by
  suffices h_dec' : dec' (p.vertices.map (λ v => List.idxOf v L.list)) by
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
        have : ¬ ( v ∈ L.list ∧ List.idxOf v' L.list < List.idxOf v L.list) := by
          intro ⟨_, h_lt⟩
          omega
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
  let q : List ℕ := p.vertices.map (λ v => List.idxOf v L.list)
  suffices q.Nodup by
    exact nodup_of_map_nodup _ _ p.vertices (λ v => List.idxOf v L.list) this
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



/-
## The main construction of Dhar's algorithm, and its consequences for orientation divisors/configurations.
-/

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

/-- The configuration asssociated to an acyclic orientation with unique source is superstable. -/
theorem orientation_config_maximal (G : CFGraph V) (O : CFOrientation G) (q : V)
    (h_acyc : is_acyclic G O) (h_unique_source : ∀ w, is_source G O w → w = q) :
    maximal_superstable G (orientation_to_config G O q h_acyc h_unique_source) := by
  dsimp [maximal_superstable]
  let cO := orientation_to_config G O q h_acyc h_unique_source
  have h_ssO : superstable G q cO := helper_orientation_config_superstable G O q h_acyc h_unique_source
  refine ⟨h_ssO, ?_⟩
  -- Goal is now just maximality of cO.
  -- Suppose another divisor is bigger. THere's an orientation divisor yet above that one.
  intro c h_ss h_ge
  rcases superstable_dhar h_ss with ⟨O', h_acyc', h_src', h_ge'⟩
  let c' := orientation_to_config G O' q h_acyc' h_src'
  -- Sandwich c between cO and c', which have the same degree
  -- These two blocks are repetitive; could factor them out
  have h_deg_le : config_degree cO ≤ config_degree c := by
    rw [config_degree]
    rw [config_degree]
    dsimp [deg]
    apply Finset.sum_le_sum
    intro v _
    exact h_ge v
  have h_deg_le' : config_degree c ≤ config_degree c' := by
    rw [config_degree]
    rw [config_degree]
    dsimp [deg]
    apply Finset.sum_le_sum
    intro v _
    exact h_ge' v
  rw [config_degree_from_O] at h_deg_le h_deg_le'
  have h_deg : config_degree c = genus G := by
    linarith
  have h_deg : config_degree c = config_degree cO := by
    rw [config_degree_from_O]
    exact h_deg
  -- Now apply config equality from degree and ge
  exact config_eq_of_ge_and_degree h_ge h_deg

/-- Every superstable configuration extends to a maximal superstable configuration -/
theorem maximal_superstable_exists (G : CFGraph V) (q : V) (c : Config V q)
    (h_super : superstable G q c) :
    ∃ c' : Config V q, maximal_superstable G c' ∧ config_ge c' c := by
    rcases superstable_dhar h_super with ⟨O, h_acyc, h_src, h_ge⟩
    let c' := orientation_to_config G O q h_acyc h_src
    use c'
    refine ⟨?_, h_ge⟩
    -- Remains to show c' is maximal superstable
    exact orientation_config_maximal G O q h_acyc h_src

/-- Every maximal superstable configuration comes from an acyclic orientation -/
theorem maximal_superstable_orientation (G : CFGraph V) (q : V) (c : Config V q)
    (h_max : maximal_superstable G c) :
    ∃ (O : CFOrientation G) (h_acyc : is_acyclic G O) (h_unique_source : ∀ w, is_source G O w → w = q),
      orientation_to_config G O q h_acyc h_unique_source = c := by
rcases superstable_dhar h_max.1 with ⟨O, h_acyc, h_src, h_ge⟩
use O, h_acyc, h_src
let c' := orientation_to_config G O q h_acyc h_src
have h_eq := h_max.2 c' (helper_orientation_config_superstable G O q h_acyc h_src) h_ge
rw [← h_eq]

/-- Proposition 4.1.11: Bijection between acyclic orientations with source q and maximal superstable configurations -/
theorem orientation_superstable_bijection (G : CFGraph V) (q : V) :
    let α := {O : CFOrientation G // is_acyclic G O ∧ (∀ w, is_source G O w → w = q)};
    let β := {c : Config V q // maximal_superstable G c};
    let f_raw : α → Config V q := λ O_sub => orientation_to_config G O_sub.val q O_sub.prop.1 O_sub.prop.2;
    let f : α → β := λ O_sub => ⟨f_raw O_sub, orientation_config_maximal G O_sub.val q O_sub.prop.1 O_sub.prop.2⟩;
    Function.Bijective f := by
  -- Define the domain and codomain types explicitly (can be removed if using let like above)
  let α := {O : CFOrientation G // is_acyclic G O ∧ (∀ w, is_source G O w → w = q)}
  let β := {c : Config V q // maximal_superstable G c}
  -- Define the function f_raw : α → Config V q
  let f_raw : α → Config V q := λ O_sub => orientation_to_config G O_sub.val q O_sub.prop.1 O_sub.prop.2
  -- Define the function f : α → β, showing the result is maximal superstable
  let f : α → β := λ O_sub =>
    ⟨f_raw O_sub, orientation_config_maximal G O_sub.val q O_sub.prop.1 O_sub.prop.2⟩

  constructor
  -- Injectivity
  { -- Prove injective f using injective f_raw
    intros O₁_sub O₂_sub h_f_eq -- h_f_eq : f O₁_sub = f O₂_sub
    have h_f_raw_eq : f_raw O₁_sub = f_raw O₂_sub := by simp at h_f_eq; exact h_f_eq

    -- Reuse original injectivity proof structure, ensuring types match
    let ⟨O₁, h₁⟩ := O₁_sub
    let ⟨O₂, h₂⟩ := O₂_sub
    -- Define c, h_eq₁, h_eq₂ based on orientation_to_config directly
    let c := orientation_to_config G O₁ q h₁.1 h₁.2
    have h_eq₁ : orientation_to_config G O₁ q h₁.1 h₁.2 = c := rfl
    have h_eq₂ : orientation_to_config G O₂ q h₂.1 h₂.2 = c := by
      exact h_f_raw_eq.symm.trans h_eq₁ -- Use transitivity

    have h_src₁ : is_source G O₁ q := by
      rcases acyclic_has_source G O₁ h₁.1 with ⟨s, hs⟩; have h_s_eq_q : s = q := h₁.2 s hs; rwa [h_s_eq_q] at hs
    have h_src₂ : is_source G O₂ q := by
      rcases acyclic_has_source G O₂ h₂.1 with ⟨s, hs⟩; have h_s_eq_q : s = q := h₂.2 s hs; rwa [h_s_eq_q] at hs

    -- Define h_super and h_max in terms of c
    have h_super : superstable G q c := by
      rw [← h_eq₁]; exact helper_orientation_config_superstable G O₁ q h₁.1 h₁.2
    have h_max   : maximal_superstable G c := by
      rw [← h_eq₁]; exact orientation_config_maximal G O₁ q h₁.1 h₁.2

    apply Subtype.ext
    -- Call helper_config_to_orientation_unique with the original h_eq₁ and h_eq₂
    exact (helper_config_to_orientation_unique G q c h_super h_max
      O₁ O₂ h₁.1 h₂.1 h_src₁ h_src₂ h₁.2 h₂.2 h_eq₁ h_eq₂)
  }

  -- Surjectivity
  { -- Prove Function.Surjective f
    unfold Function.Surjective
    intro y -- y should now have type β
    -- Access components using .val and .property
    let c_target : Config V q := y.val -- Explicitly type c_target
    let h_target_max_superstable := y.property

    -- Use the fact that every maximal superstable config comes from an orientation.
    rcases maximal_superstable_orientation G q c_target h_target_max_superstable with
      ⟨O, h_acyc, h_unique_source, h_config_eq_target⟩

    -- Construct the required subtype element x : α (the pre-image)
    let x : α := ⟨O, ⟨h_acyc, h_unique_source⟩⟩

    -- Show that this x exists
    use x

    -- Show f x = y using Subtype.eq
    apply Subtype.ext
    -- Goal: (f x).val = y.val
    -- Need to show: f_raw x = c_target
    -- This is exactly h_config_eq_target
    exact h_config_eq_target
    -- Proof irrelevance handles the equality of the property components.
  }
