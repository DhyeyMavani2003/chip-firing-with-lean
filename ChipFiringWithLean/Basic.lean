import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Tactic
import Mathlib.Algebra.Ring.Int

import Init.Core
import Init.NotationExtra

import Paperproof

set_option linter.unusedVariables false
set_option trace.split.failure true
set_option linter.unusedSectionVars false

open Multiset Finset

-- Assume V is a finite type with decidable equality
variable {V : Type} [DecidableEq V] [Fintype V]

-- Define a set of edges to be loopless only if it doesn't have loops
def isLoopless (edges : Multiset (V × V)) : Bool :=
  Multiset.card (edges.filter (λ e => (e.1 = e.2))) = 0

def isLoopless_prop (edges : Multiset (V × V)) : Prop :=
  ∀ v, (v, v) ∉ edges

lemma isLoopless_prop_bool_equiv (edges : Multiset (V × V)) :
    isLoopless_prop edges ↔ isLoopless edges = true := by
  unfold isLoopless_prop isLoopless
  constructor
  · intro h
    apply decide_eq_true
    rw [Multiset.card_eq_zero]
    simp only [Multiset.eq_zero_iff_forall_not_mem]
    intro e he
    have h_eq : e.1 = e.2 := by
      exact Multiset.mem_filter.mp he |>.2
    have he' : e ∈ edges := by
      exact Multiset.mem_filter.mp he |>.1
    cases e with
    | mk a b =>
      simp at h_eq
      have : (a, b) = (a, a) := by rw [h_eq]
      rw [this] at he'
      exact h a he'

  · intro h
    intro v
    intro hv
    apply False.elim
    have h_filter : (v, v) ∈ Multiset.filter (λ e => e.1 = e.2) edges := by
      apply Multiset.mem_filter.mpr
      constructor
      · exact hv
      · simp

    have h_card : Multiset.card (Multiset.filter (λ e => e.1 = e.2) edges) > 0 := by
      apply Multiset.card_pos_iff_exists_mem.mpr
      exists (v, v)

    have h_eq : Multiset.card (Multiset.filter (λ e => e.1 = e.2) edges) = 0 := by
      -- Use the fact that isLoopless edges = true means the cardinality is 0
      unfold isLoopless at h
      -- Since h : decide (...) = true, we extract the underlying proposition
      apply of_decide_eq_true h

    linarith

-- Define a set of edges to be undirected only if it doesn't have both (v, w) and (w, v)
def isUndirected (edges : Multiset (V × V)) : Bool :=
  Multiset.card (edges.filter (λ e => (e.2, e.1) ∈ edges)) = 0

def isUndirected_prop (edges : Multiset (V × V)) : Prop :=
  ∀ v1 v2, (v1, v2) ∈ edges → (v2, v1) ∉ edges

lemma isUndirected_prop_bool_equiv (edges : Multiset (V × V)) :
    isUndirected_prop edges ↔ isUndirected edges = true := by
  unfold isUndirected_prop isUndirected
  constructor
  · intro h_prop -- Assume isUndirected_prop edges
    apply decide_eq_true -- Goal: decide (...) = true
    rw [Multiset.card_eq_zero] -- Goal: filter (...) = 0
    simp only [Multiset.eq_zero_iff_forall_not_mem] -- Goal: ∀ (a : V × V), a ∉ filter (...) edges
    intro e he_filter -- Assume e ∈ filter (...) edges
    -- Unpack he_filter
    have h_mem_edges : e ∈ edges := Multiset.mem_filter.mp he_filter |>.1
    have h_rev_mem_edges : (e.2, e.1) ∈ edges := Multiset.mem_filter.mp he_filter |>.2
    -- Use h_prop to get a contradiction
    exact h_prop e.1 e.2 h_mem_edges h_rev_mem_edges
  · intro h_bool -- Assume isUndirected edges = true
    intro v1 v2 h_v1v2_mem h_v2v1_mem -- Assume v1, v2, (v1, v2) ∈ edges, (v2, v1) ∈ edges. Goal: False
    apply False.elim
    -- Show (v1, v2) is in the filtered multiset
    have h_filter_mem : (v1, v2) ∈ Multiset.filter (λ e => (e.2, e.1) ∈ edges) edges := by
      apply Multiset.mem_filter.mpr
      constructor
      · exact h_v1v2_mem -- (v1, v2) ∈ edges
      · simp -- Goal: ((v1, v2).2, (v1, v2).1) ∈ edges
        exact h_v2v1_mem -- (v2, v1) ∈ edges
    -- The card of the filtered multiset must be > 0
    have h_card_pos : Multiset.card (Multiset.filter (λ e => (e.2, e.1) ∈ edges) edges) > 0 := by
      apply Multiset.card_pos_iff_exists_mem.mpr
      exists (v1, v2)
    -- Get card = 0 from h_bool
    have h_card_zero : Multiset.card (Multiset.filter (λ e => (e.2, e.1) ∈ edges) edges) = 0 := by
      apply of_decide_eq_true h_bool
    -- Contradiction
    linarith -- h_card_pos contradicts h_card_zero


-- Multigraph with undirected and loopless edges
structure CFGraph (V : Type) [DecidableEq V] [Fintype V] :=
  (edges : Multiset (V × V))
  (loopless : isLoopless edges = true)
  (undirected: isUndirected edges = true)

-- Divisor as a function from vertices to integers
def CFDiv (V : Type) := V → ℤ

-- Make CFDiv an Additive Commutative Group
instance : AddCommGroup (CFDiv V) := Pi.addCommGroup

-- Divisor addition (pointwise)
instance : Add (CFDiv V) := ⟨λ D₁ D₂ => λ v => D₁ v + D₂ v⟩

-- Divisor subtraction (pointwise)
instance : Sub (CFDiv V) := ⟨λ D₁ D₂ => λ v => D₁ v - D₂ v⟩

-- Zero divisor
instance : Zero (CFDiv V) := ⟨λ _ => 0⟩

-- Neg for divisors
instance : Neg (CFDiv V) := ⟨λ D => λ v => -D v⟩

-- Add coercion from V → ℤ to CFDiv V
instance : Coe (V → ℤ) (CFDiv V) where
  coe f := f

-- Properties of divisor arithmetic
@[simp] lemma add_apply (D₁ D₂ : CFDiv V) (v : V) :
  (D₁ + D₂) v = D₁ v + D₂ v := rfl

@[simp] lemma sub_apply (D₁ D₂ : CFDiv V) (v : V) :
  (D₁ - D₂) v = D₁ v - D₂ v := rfl

@[simp] lemma zero_apply (v : V) :
  (0 : CFDiv V) v = 0 := rfl

@[simp] lemma neg_apply (D : CFDiv V) (v : V) :
  (-D) v = -(D v) := rfl

@[simp] lemma distrib_sub_add (D₁ D₂ D₃ : CFDiv V) :
  D₁ - (D₂ + D₃) = (D₁ - D₂) - D₃ := by
  funext x
  simp [sub_apply, add_apply]
  ring

@[simp] lemma add_sub_distrib (D₁ D₂ D₃ : CFDiv V) :
  (D₁ + D₂) - D₃ = (D₁ - D₃) + D₂ := by
  funext x
  simp [sub_apply, add_apply]
  ring

/-- Lemma: Lambda form of divisor subtraction equals standard form -/
lemma divisor_sub_eq_lambda (G : CFGraph V) (D₁ D₂ : CFDiv V) :
  (λ v => D₁ v - D₂ v) = D₁ - D₂ := by
  funext v
  simp [sub_apply]

-- Number of edges between two vertices as an integer
def num_edges (G : CFGraph V) (v w : V) : ℕ :=
  Multiset.card (G.edges.filter (λ e => e = (v, w) ∨ e = (w, v)))

-- Lemma: Number of edges is non-negative
lemma num_edges_nonneg (G : CFGraph V) (v w : V) :
  num_edges G v w ≥ 0 := by
  exact Nat.zero_le (num_edges G v w)

-- Degree (Valence) of a vertex as an integer (defined as the sum of incident edge multiplicities)
def vertex_degree (G : CFGraph V) (v : V) : ℤ :=
  ∑ u : V, (num_edges G v u : ℤ)

-- Vertex degree equals the same sum by definition
@[simp]
lemma vertex_degree_eq_sum_num_edges (G : CFGraph V) (v : V) :
  vertex_degree G v = ∑ u : V, (num_edges G v u : ℤ) := by
  rfl

-- Vertex degree is non-negative
lemma vertex_degree_nonneg (G : CFGraph V) (v : V) :
  vertex_degree G v ≥ 0 := by
  unfold vertex_degree
  apply Finset.sum_nonneg
  intro u _
  exact Int.ofNat_nonneg _

-- An edge cannot connect a vertex to itself in a loopless graph, so there are zero such edges.
lemma num_edges_self_eq_zero (G : CFGraph V) (v : V) :
  num_edges G v v = 0 := by
  unfold num_edges
  rw [Multiset.card_eq_zero] -- Goal: filter ... = 0
  apply Multiset.filter_eq_nil.mpr
  intro e h_edge_in_G_edges h_edge_is_loop_form -- e ∈ G.edges and e = (v,v) ∨ e = (v,v)
  simp only [or_self] at h_edge_is_loop_form -- e = (v,v)
  rw [h_edge_is_loop_form] at h_edge_in_G_edges -- (v,v) ∈ G.edges
  have h_loopless_prop : isLoopless_prop G.edges :=
    (isLoopless_prop_bool_equiv G.edges).mpr G.loopless
  exact h_loopless_prop v h_edge_in_G_edges -- Contradiction: (v,v) ∈ G.edges and isLoopless_prop

-- Vertex degree equals the sum over neighbours other than the vertex itself.
lemma vertex_degree_eq_sum_incident_edges (G : CFGraph V) (v : V) :
  (vertex_degree G v : ℤ) = ∑ w in Finset.univ.erase v, (num_edges G v w : ℤ) := by
  unfold vertex_degree
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ v) (f := λ w => (num_edges G v w : ℤ))]
  rw [num_edges_self_eq_zero G v]
  rw [Nat.cast_zero] -- Cast 0 from ℕ to ℤ
  rw [zero_add]
  rw [Finset.sdiff_singleton_eq_erase]

-- Definition of the graph Laplacian map
-- Maps a firing vector (V → ℤ) to a principal divisor (CFDiv V)
def laplacian_map (G : CFGraph V) (x : V → ℤ) : CFDiv V :=
  λ v => (vertex_degree G v : ℤ) * x v - ∑ u : V, ↑(num_edges G v u) * x u

-- Set of principal divisors, defined as the image of the Laplacian map
def principal_divisors_laplacian (G : CFGraph V) : AddSubgroup (CFDiv V) :=
  AddSubgroup.closure (Set.range (laplacian_map G))

-- Firing move at a vertex
def firing_move (G : CFGraph V) (D : CFDiv V) (v : V) : CFDiv V :=
  λ w => if w = v then D v - vertex_degree G v else D w + num_edges G v w

-- Borrowing move at a vertex
def borrowing_move (G : CFGraph V) (D : CFDiv V) (v : V) : CFDiv V :=
  λ w => if w = v then D v + vertex_degree G v else D w - num_edges G v w

-- Define finset_sum using Finset.fold
def finset_sum {α β} [AddCommMonoid β] (s : Finset α) (f : α → β) : β :=
  s.fold (· + ·) 0 f

-- Define set_firing to use finset_sum with consistent types
def set_firing (G : CFGraph V) (D : CFDiv V) (S : Finset V) : CFDiv V :=
  λ w => D w + finset_sum S (λ v => if w = v then -vertex_degree G v else num_edges G v w)

-- Define the group structure on CFDiv V
instance : AddGroup (CFDiv V) := Pi.addGroup

-- Define the firing vector for a single vertex
def firing_vector (G : CFGraph V) (v : V) : CFDiv V :=
  λ w => if w = v then -vertex_degree G v else num_edges G v w

lemma firing_move_eq_add_firing_vector (G : CFGraph V) (D : CFDiv V) (v : V) :
  firing_move G D v = D + firing_vector G v := by
  unfold firing_move firing_vector
  funext w
  dsimp
  by_cases h_eq : w = v
  · -- Case w = v
    simp [h_eq]
    ring
  · -- Case w ≠ v
    simp [h_eq]

-- Define the firing vector for a set of vertices
def set_firing_vector (G : CFGraph V) (D : CFDiv V) (S : Finset V) : CFDiv V :=
  λ w => finset_sum S (λ v => if w = v then -vertex_degree G v else num_edges G v w)

-- Lemma: Set firing equals adding the set firing vector
lemma set_firing_eq_add_set_firing_vector (G : CFGraph V) (D : CFDiv V) (S : Finset V) :
  set_firing G D S = D + set_firing_vector G D S := by
  unfold set_firing set_firing_vector
  funext w
  dsimp

-- Define the principal divisors generated by firing moves at vertices
def principal_divisors (G : CFGraph V) : AddSubgroup (CFDiv V) :=
  AddSubgroup.closure (Set.range (firing_vector G))

-- Lemma: Principal divisors contain the firing vector at a vertex
lemma mem_principal_divisors_firing_vector (G : CFGraph V) (v : V) :
  firing_vector G v ∈ principal_divisors G := by
  apply AddSubgroup.subset_closure
  apply Set.mem_range_self

-- Define linear equivalence of divisors
def linear_equiv (G : CFGraph V) (D D' : CFDiv V) : Prop :=
  D' - D ∈ principal_divisors G

-- [Proven] Proposition: Linear equivalence is an equivalence relation on Div(G)
theorem linear_equiv_is_equivalence (G : CFGraph V) : Equivalence (linear_equiv G) := by
  apply Equivalence.mk
  -- Reflexivity
  · intro D
    unfold linear_equiv
    have h_zero : D - D = 0 := by simp
    rw [h_zero]
    exact AddSubgroup.zero_mem _

  -- Symmetry
  · intros D D' h
    unfold linear_equiv at *
    have h_symm : D - D' = -(D' - D) := by simp [sub_eq_add_neg, neg_sub]
    rw [h_symm]
    exact AddSubgroup.neg_mem _ h

  -- Transitivity
  · intros D D' D'' h1 h2
    unfold linear_equiv at *
    have h_trans : D'' - D = (D'' - D') + (D' - D) := by simp
    rw [h_trans]
    exact AddSubgroup.add_mem _ h2 h1

-- Define divisor class determined by a divisor
def divisor_class (G : CFGraph V) (D : CFDiv V) : Set (CFDiv V) :=
  {D' : CFDiv V | linear_equiv G D D'}

-- Define effective divisors (in terms of non-negativity, returning a Bool)
def effective_bool (D : CFDiv V) : Bool :=
  ↑((Finset.univ.filter (fun v => D v < 0)).card = 0)

-- Define effective divisors (in terms of equivalent Prop)
def effective (D : CFDiv V) : Prop :=
  ∀ v : V, D v ≥ 0

-- Define the set of effective divisors
-- Note: We use the Prop returned by `effective` in set comprehension
def Div_plus (G : CFGraph V) : Set (CFDiv V) :=
  {D : CFDiv V | effective D}

-- Define winnable divisor
-- Note: We use the Prop returned by `linear_equiv` in set comprehension
def winnable (G : CFGraph V) (D : CFDiv V) : Prop :=
  ∃ D' ∈ Div_plus G, linear_equiv G D D'

-- Define the complete linear system of divisors
def complete_linear_system (G: CFGraph V) (D: CFDiv V) : Set (CFDiv V) :=
  {D' : CFDiv V | linear_equiv G D D' ∧ effective D'}

-- Degree of a divisor
def deg (D : CFDiv V) : ℤ := ∑ v, D v
def deg_prop (D : CFDiv V) : Prop := deg D = ∑ v, D v

lemma deg_firing_vector_eq_zero (G : CFGraph V) (v_fire : V) :
  deg (firing_vector G v_fire) = 0 := by
  unfold deg firing_vector
  rw [Finset.sum_ite]
  have h_filter_eq_single : Finset.filter (fun x => x = v_fire) univ = {v_fire} := by
    ext x; simp [eq_comm]
  rw [h_filter_eq_single, Finset.sum_singleton]
  have h_filter_eq_erase : Finset.filter (fun x => ¬x = v_fire) univ = Finset.univ.erase v_fire := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_erase, and_true, true_and]
  rw [h_filter_eq_erase]
  rw [← vertex_degree_eq_sum_incident_edges G v_fire]
  simp

lemma deg_add (D₁ D₂ : CFDiv V) : deg (D₁ + D₂) = deg D₁ + deg D₂ := by
  unfold deg
  simp only [add_apply, Finset.sum_add_distrib]

lemma deg_zero : deg (0 : CFDiv V) = 0 := by
  unfold deg
  simp only [zero_apply, Finset.sum_const_zero]

lemma deg_neg (D : CFDiv V) : deg (-D) = - deg D := by
  unfold deg
  simp only [neg_apply, Finset.sum_neg_distrib]

theorem linear_equiv_preserves_deg (G : CFGraph V) (D D' : CFDiv V) (h_equiv : linear_equiv G D D') :
  deg D = deg D' := by
  unfold linear_equiv at h_equiv
  have h_deg_diff_zero : deg (D' - D) = 0 := by
    refine AddSubgroup.closure_induction h_equiv ?_ ?_ ?_ ?_
    · -- Case 1: Elements from S = Set.range (firing_vector G)
      intro x hx_in_S -- hx_in_S : x ∈ Set.range (firing_vector G)
      -- Goal: deg x = 0
      rcases hx_in_S with ⟨v, rfl⟩ -- Destructure hx_in_S to get v and substitute x = firing_vector G v
      exact deg_firing_vector_eq_zero G v
    · -- Case 2: The zero element
      -- Goal: deg 0 = 0
      exact deg_zero
    · -- Case 3: Sum of two elements satisfying the property
      intro x y hx_deg_zero hy_deg_zero -- hx_deg_zero: deg x = 0, hy_deg_zero: deg y = 0
      -- Goal: deg (x + y) = 0
      rw [deg_add, hx_deg_zero, hy_deg_zero, add_zero]
    · -- Case 4: Negative of an element satisfying the property
      intro x hx_deg_zero -- hx_deg_zero: deg x = 0
      -- Goal: deg (-x) = 0
      rw [deg_neg, hx_deg_zero, neg_zero]

  have h_deg_sub_eq_sub_deg : deg (D' - D) = deg D' - deg D := by
    simp [sub_eq_add_neg, deg_add, deg_neg]

  rw [h_deg_sub_eq_sub_deg] at h_deg_diff_zero
  linarith [h_deg_diff_zero]

-- Define a firing script as a function from vertices to integers
def firing_script (V : Type) := V → ℤ

-- Define Laplacian matrix as an |V| x |V| integer matrix
open Matrix
variable [Fintype V]

def laplacian_matrix (G : CFGraph V) : Matrix V V ℤ :=
  λ i j => if i = j then vertex_degree G i else - (num_edges G i j)

-- Note: The Laplacian matrix L is given by Deg(G) - A, where Deg(G) is the diagonal matrix of degrees and A is the adjacency matrix.
-- This matrix can be used to represent the effect of a firing script on a divisor.

-- Apply the Laplacian matrix to a firing script, and current divisor to get a new divisor
def apply_laplacian (G : CFGraph V) (σ : firing_script V) (D: CFDiv V) : CFDiv V :=
  fun v => (D v) - (laplacian_matrix G).mulVec σ v

-- Define q-reduced divisors
def q_reduced (G : CFGraph V) (q : V) (D : CFDiv V) : Prop :=
  (∀ v ∈ {v | v ≠ q}, D v ≥ 0) ∧
  (∀ S : Finset V, S ⊆ (Finset.univ.filter (λ v => v ≠ q)) → S.Nonempty →
    ∃ v ∈ S, D v < ∑ w in (univ.filter (λ x => x ≠ q)).filter (λ x => x ∉ S), (num_edges G v w : ℤ))

-- Define the ordering of divisors
def divisor_order (G : CFGraph V) (q : V) (D D' : CFDiv V) : Prop :=
  (∃ T : Finset V, T ⊆ (Finset.univ.filter (λ v => v ≠ q)) ∧ D' = set_firing G D T) ∧
  (∀ T' : Finset V, T' ⊆ (Finset.univ.filter (λ v => v ≠ q)) → D' ≠ set_firing G D T')

-- Define the ordering of divisors using the divisor_order relation
def divisor_ordering (G : CFGraph V) (q : V) (D D' : CFDiv V) : Prop :=
  divisor_order G q D' D

-- Legal set-firing: Ensure no vertex in S is in debt after firing
def legal_set_firing (G : CFGraph V) (D : CFDiv V) (S : Finset V) : Prop :=
  ∀ v ∈ S, set_firing G D S v ≥ 0

lemma degree_of_firing_vector_is_zero (G : CFGraph V) (v_node : V) :
  deg (firing_vector G v_node) = 0 := by
  unfold deg firing_vector
  simp only [Finset.sum_ite]
  rw [vertex_degree_eq_sum_incident_edges G v_node]
  have h_filter_eq_diff : Finset.filter (fun x => ¬x = v_node) Finset.univ = Finset.univ \ {v_node} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_singleton]
  have h_filter_eq_single : Finset.filter (fun x => x = v_node) Finset.univ = {v_node} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, eq_comm]
  rw [h_filter_eq_diff, h_filter_eq_single]
  simp

lemma degree_of_principal_divisor_is_zero (G : CFGraph V) (h : CFDiv V) :
  h ∈ principal_divisors G → deg h = 0 := by
  intro h_mem_princ
  -- principal_divisors is AddSubgroup.closure (Set.range (firing_vector G))
  -- Use induction on the structure of the subgroup
  refine AddSubgroup.closure_induction h_mem_princ ?_ ?_ ?_ ?_
  · -- Case 1: h is in the range of firing_vector G
    intro x hx_in_range
    rcases hx_in_range with ⟨v, rfl⟩
    exact degree_of_firing_vector_is_zero G v
  · -- Case 2: h = 0 (the zero divisor)
    simp [deg]
  · -- Case 3: h = x + y where deg x = 0 and deg y = 0
    intros x y h_deg_x_zero h_deg_y_zero
    rw [deg_add, h_deg_x_zero, h_deg_y_zero, add_zero]
  · -- Case 4: h = -x where deg x = 0
    intros x h_deg_x_zero
    rw [deg_neg, h_deg_x_zero, neg_zero]

/- [IN-PROGRESS LEMMA] Q-reduced form uniquely determines divisor class.

-- Proof idea:
  intro h
  cases h with
  | intro h_qred_D1 h_rest =>
    cases h_rest with
    | intro h_qred_D2 h_lin_equiv =>
      let h_diff := D₁ - D₂
      have h_diff_is_principal : h_diff ∈ principal_divisors G := by
        unfold linear_equiv at h_lin_equiv
        -- Fix the definition issue - linear_equiv is D₂ - D₁ ∈ principal_divisors G
        -- but h_diff is D₁ - D₂
        have h_neg : -(D₂ - D₁) = D₁ - D₂ := by
          simp only [neg_sub]
        have h_prin_neg : -(D₂ - D₁) ∈ principal_divisors G := by
          apply AddSubgroup.neg_mem
          exact h_lin_equiv
        rw [h_neg] at h_prin_neg
        exact h_prin_neg

      -- The rest of the proof involves showing that a q-reduced principal divisor must be zero
      -- This is a key theorem in chip-firing theory
      sorry
-/
axiom q_reduced_unique_class (G : CFGraph V) (q : V) (D₁ D₂ : CFDiv V) :
  q_reduced G q D₁ ∧ q_reduced G q D₂ ∧ linear_equiv G D₁ D₂ → D₁ = D₂

lemma principal_divisor_is_q_reduced_implies_zero (G : CFGraph V) (q_vertex : V) (τ : CFDiv V) :
  τ ∈ principal_divisors G → q_reduced G q_vertex τ → τ = 0 := by
  intros h_τ_principal h_τ_q_reduced
  by_contra h_τ_neq_zero

  have h_deg_τ_zero : deg τ = 0 := degree_of_principal_divisor_is_zero G τ h_τ_principal

  let V' := Finset.univ.filter (λ v => v ≠ q_vertex)
  have h_τ_q_reduced_cond1 : ∀ v ∈ V', τ v ≥ 0 := by
    convert h_τ_q_reduced.left
    funext v; simp [V']
  have h_τ_q_reduced_cond2 : ∀ (S : Finset V), S ⊆ V' → S.Nonempty →
    (∃ v ∈ S, τ v < ∑ w in V'.filter (λ x => x ∉ S), (num_edges G v w : ℤ)) := h_τ_q_reduced.right

  have V'_nonempty_or_τ_is_zero : (V' = ∅ → τ = 0) := by
    intro h_V'_is_empty
    have h_deg_τ_eq_τ_q : deg τ = τ q_vertex := by
      unfold deg;
      have univ_eq_singleton : Finset.univ = {q_vertex} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine' ⟨Finset.mem_univ q_vertex, ?_⟩
        intro x _;
        by_cases hx_eq_q : x = q_vertex
        · exact hx_eq_q
        · exact (Finset.not_mem_empty x (h_V'_is_empty ▸ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx_eq_q⟩ : x ∈ V'))).elim
      rw [univ_eq_singleton, Finset.sum_singleton]
    rw [h_deg_τ_eq_τ_q] at h_deg_τ_zero
    funext v
    by_cases hv_eq_q : v = q_vertex
    · rw [hv_eq_q, h_deg_τ_zero]; rfl
    · have h_v_in_V' : v ∈ V' := Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv_eq_q⟩
      rw [h_V'_is_empty] at h_v_in_V'
      exact absurd h_v_in_V' (Finset.not_mem_empty v)

  have V'_nonempty : V'.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h_V'_eq_empty_proof
    apply h_τ_neq_zero
    exact V'_nonempty_or_τ_is_zero h_V'_eq_empty_proof

  have h_τ_q_lt_zero : τ q_vertex < 0 := by
    have sum_V'_nonneg : ∑ v in V', τ v ≥ 0 := by
      apply Finset.sum_nonneg
      intro v hv_in_V'
      exact h_τ_q_reduced_cond1 v hv_in_V'

    have h_deg_τ_expanded : τ q_vertex + ∑ v in V', τ v = 0 := by
      unfold deg at h_deg_τ_zero
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := λ v' => v' ≠ q_vertex)] at h_deg_τ_zero
      rw [add_comm] at h_deg_τ_zero
      have h_sum_filter_not : ∑ v in Finset.filter (λ v' => ¬(v' ≠ q_vertex)) Finset.univ, τ v = τ q_vertex := by
        have h_filter_eq : Finset.filter (λ v' => ¬(v' ≠ q_vertex)) Finset.univ = {q_vertex} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          exact ⟨λ h => not_not.mp h, λ h => not_not.mpr h⟩
        rw [h_filter_eq]
        simp only [Finset.sum_singleton]
      rw [h_sum_filter_not] at h_deg_τ_zero
      have h_sum_filter_eq : ∑ v in Finset.filter (λ v' => v' ≠ q_vertex) Finset.univ, τ v = ∑ v in V', τ v := by rfl
      rw [h_sum_filter_eq] at h_deg_τ_zero
      exact h_deg_τ_zero

    have h_τ_q_le_zero : τ q_vertex ≤ 0 := by
      linarith [h_deg_τ_expanded, sum_V'_nonneg]

    apply lt_of_le_of_ne h_τ_q_le_zero
    intro h_τ_q_eq_zero

    have sum_V'_eq_zero : ∑ v in V', τ v = 0 := by
      rw [h_τ_q_eq_zero] at h_deg_τ_expanded
      simp only [zero_add] at h_deg_τ_expanded
      exact h_deg_τ_expanded

    have all_V'_zero : ∀ v ∈ V', τ v = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg (λ v hv => h_τ_q_reduced_cond1 v hv)).mp sum_V'_eq_zero

    have τ_is_zero : τ = 0 := by
      funext v
      by_cases h_v_eq_q : v = q_vertex
      · rw [h_v_eq_q, h_τ_q_eq_zero]; rfl
      · exact all_V'_zero v (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h_v_eq_q⟩)

    exact h_τ_neq_zero τ_is_zero

  specialize h_τ_q_reduced_cond2 V' (le_refl V') V'_nonempty
  cases h_τ_q_reduced_cond2 with
  | intro v₀ h_v₀_in_V'_and_lt_sum =>
    have h_v₀_in_V' : v₀ ∈ V' := h_v₀_in_V'_and_lt_sum.1
    have h_τ_v₀_lt_sum : τ v₀ < ∑ w in V'.filter (λ x => x ∉ V'), (num_edges G v₀ w : ℤ) :=
      h_v₀_in_V'_and_lt_sum.2

    have h_filter_is_empty : V'.filter (λ x => x ∉ V') = ∅ := by
      rw [Finset.filter_eq_empty_iff]; intro x; simp;
    rw [h_filter_is_empty, Finset.sum_empty] at h_τ_v₀_lt_sum
    have h_τ_v₀_ge_zero : τ v₀ ≥ 0 := h_τ_q_reduced_cond1 v₀ h_v₀_in_V'
    exact absurd h_τ_v₀_lt_sum (not_lt.mpr h_τ_v₀_ge_zero)
