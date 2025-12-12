import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Order.Lemmas
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Order.WellFounded
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lemmas
import Mathlib.Data.List.Cycle
import Mathlib.Data.List.Nodup
import ChipFiringWithLean.Basic
import ChipFiringWithLean.Config
import Paperproof
import Mathlib.Data.List.Defs

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

lemma ordiv_unwinnable (G : CFGraph V) (O : CFOrientation G) :
  ¬ winnable G (ordiv G O) := by
  sorry


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
