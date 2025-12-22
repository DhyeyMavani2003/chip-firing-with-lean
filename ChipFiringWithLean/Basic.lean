import Mathlib.Tactic

import Init.Core
import Init.NotationExtra

import Paperproof

set_option linter.unusedVariables false
set_option trace.split.failure true
set_option linter.unusedSectionVars false

open Multiset Finset

-- Assume V is a finite type with decidable equality
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]

def isLoopless (edges : Multiset (V × V)) : Prop :=
  ∀ v, (v, v) ∉ edges

-- Multigraph with loopless edges
structure CFGraph (V : Type) [DecidableEq V] [Fintype V] [Nonempty V]:=
  (edges : Multiset (V × V))
  (loopless : isLoopless edges)

/-- The genus of a graph is its cycle rank: |E| - |V| + 1 -/
def genus (G : CFGraph V) : ℤ :=
  Multiset.card G.edges - Fintype.card V + 1

-- Number of edges between two vertices as an integer
-- It is preferable to use this function to access the graph structrue rather than accessing G.edges directly, in case the implementation changes.
def num_edges (G : CFGraph V) (v w : V) : ℕ :=
  Multiset.card (G.edges.filter (λ e => e = (v, w) ∨ e = (w, v)))

def graph_connected (G : CFGraph V) : Prop :=
  ∀ S : Finset V, (∃ (v w : V), v ∈ S ∧ w ∉ S) →
    (∃ v ∈ S, ∃ w ∉ S, num_edges G v w > 0)

-- Divisor as a function from vertices to integers
def CFDiv (V : Type) := V → ℤ

/-- A divisor with one chip at a specified vertex `v_chip` and zero chips elsewhere. -/
def one_chip (v_chip : V) : CFDiv V :=
  fun v => if v = v_chip then 1 else 0

@[simp] lemma one_chip_apply_v (v : V) : one_chip v v = 1 := by
  dsimp [one_chip]
  rw [if_pos rfl]

@[simp] lemma one_chip_apply_other (v w : V) : v ≠ w → one_chip v w = 0 := by
  simp [one_chip]
  intro h
  contrapose! h
  rw [h]

@[simp] lemma one_chip_apply_other' (v w : V) : w ≠ v → one_chip v w = 0 := by
  simp [one_chip]

-- Make CFDiv an Additive Commutative Group
instance : AddCommGroup (CFDiv V) := Pi.addCommGroup

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

@[simp] lemma smul_apply (n : ℤ) (D : CFDiv V) (v : V) :
  (n • D) v = n * (D v) := by
  rfl

/-- Lemma: Lambda form of divisor subtraction equals standard form -/
lemma divisor_sub_eq_lambda (G : CFGraph V) (D₁ D₂ : CFDiv V) :
  (D₁ - D₂) = D₁ - D₂ := by
  funext v
  simp [sub_apply]

-- Lemma: Number of edges is non-negative
lemma num_edges_nonneg (G : CFGraph V) (v w : V) :
  num_edges G v w ≥ 0 := by
  exact Nat.zero_le (num_edges G v w)

-- Lemma: Number of edges is symmetric
lemma num_edges_symmetric (G : CFGraph V) (v w : V) :
  num_edges G v w = num_edges G w v := by
  unfold num_edges
  simp [Or.comm]

lemma num_edges_self_zero (G : CFGraph V) (v : V) :
  num_edges G v v = 0 := by
  unfold num_edges
  rw [Multiset.card_eq_zero]
  apply Multiset.filter_eq_nil.mpr
  intro a h_inE h_eq_loop
  rw [or_self] at h_eq_loop
  rw [h_eq_loop] at h_inE
  exact G.loopless v h_inE



-- degree (valence) of a vertex as an integer (defined as the sum of incident edge multiplicities)
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
  exact G.loopless v h_edge_in_G_edges -- Contradiction: (v,v) ∈ G.edges and isLoopless_prop

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

-- Give CFDiv V the structure of a poset
instance : PartialOrder (CFDiv V) :=
  {
    le := λ D₁ D₂ => ∀ v : V, D₁ v ≤ D₂ v,
    le_refl := by
      intro D v
      exact le_refl <| D v,
    le_trans := by
      intro D₁ D₂ D₃ h₁₂ h₂₃ v
      exact le_trans (h₁₂ v) (h₂₃ v),
    le_antisymm := by
      intro D₁ D₂ h₁₂ h₂₁
      funext v
      exact le_antisymm (h₁₂ v) (h₂₁ v)
  }


-- Define effective divisors (in terms of equivalent Prop)
def effective (D : CFDiv V) : Prop :=
  ∀ v : V, D v ≥ 0
  -- alternative: just say D ≥ 0. Requires changes elsewhere,

-- Simple example: one_chip is effective.
-- [TODO] Is this somewhere else in the code already?
def eff_one_chip (v : V) : effective (one_chip v) := by
  intro w
  dsimp [one_chip]
  by_cases h_eq : w = v
  · -- Case w = v
    rw [h_eq]
    simp
  · -- Case w ≠ v
    simp [h_eq]

lemma eff_iff_geq_zero (D : CFDiv V) : effective D ↔ D ≥ 0:= by
  rfl

lemma sub_eff_iff_geq (D₁ D₂ : CFDiv V) : effective (D₁ - D₂) ↔ D₁ ≥ D₂ := by
  rw [eff_iff_geq_zero]
  constructor
  intro h v
  specialize h v
  simp at h
  linarith
  intro h v
  specialize h v
  simp
  linarith

lemma eff_of_eff_add_eff (D₁ D₂ : CFDiv V) :
  effective D₁ → effective D₂ → effective (D₁ + D₂) := by
  intro h_eff1 h_eff2 v
  unfold effective at *
  specialize h_eff1 v
  specialize h_eff2 v
  simp [add_apply]
  linarith



lemma eff_of_smul_eff (n : ℕ) (D : CFDiv V) :
  effective D → effective (n • D) := by
  intro h_eff v
  unfold effective at *
  specialize h_eff v
  simp [smul_apply]
  apply Int.mul_nonneg
  · exact Int.ofNat_nonneg n
  · exact h_eff

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
def deg : CFDiv V →+ ℤ := {
  toFun := λ D => ∑ v, D v,
  map_zero' := by
    simp [Finset.sum_const_zero],
  map_add' := by
    intro D₁ D₂
    simp [Finset.sum_add_distrib],
}

@[simp] lemma deg_one_chip (v : V) : deg (one_chip v) = 1 := by
  dsimp [deg, one_chip]
  rw [Finset.sum_ite]
  have h_filter_eq_single : Finset.filter (fun x => x = v) Finset.univ = {v} := by
    ext x; simp [eq_comm]
  rw [h_filter_eq_single, Finset.sum_singleton]
  have h_filter_eq_erase : Finset.filter (fun x => ¬x = v) Finset.univ = Finset.univ.erase v := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_erase, and_true, true_and]
  rw [h_filter_eq_erase]
  simp

lemma deg_of_eff_nonneg (D : CFDiv V) :
  effective D → deg D ≥ 0 := by
  intro h_eff
  refine Finset.sum_nonneg ?_
  intro v _
  specialize h_eff v
  exact h_eff

-- [TODO]: this proof can probably be simplified
lemma eff_degree_zero (D : CFDiv V) : effective D → deg D = 0 → D = 0 := by
  intro h_eff h_deg_
  funext v; simp
  by_contra h_chip
  have h_chip_pos : D v ≥ 1 := by
    have trich := lt_trichotomy (D v) 0
    rcases trich with h_neg | h_zero | h_pos
    · -- Case D v < 0
      exfalso
      linarith [h_eff v]
    · -- Case D v = 0
      exfalso
      exact h_chip h_zero
    · -- Case D v > 0
      exact Int.pos_iff_one_le.mp h_pos
  let D' := D - one_chip v
  have D'_eff : effective D' := by
    intro w
    by_cases h_eq : w = v
    · -- Case w = v
      rw [h_eq]
      dsimp [D']
      simp [one_chip]
      exact h_chip_pos
    · -- Case w ≠ v
      dsimp [D']
      simp [one_chip, h_eq]
      exact h_eff w
  have h_deg_D' : deg D' = -1 := by
    dsimp [D']
    simp
    rw [h_deg_]
  have h_nonneg := deg_of_eff_nonneg D' D'_eff
  linarith

lemma deg_firing_vector_eq_zero (G : CFGraph V) (v_fire : V) :
  deg (firing_vector G v_fire) = 0 := by
  dsimp [deg, firing_vector]
  rw [Finset.sum_ite]
  have h_filter_eq_single : Finset.filter (fun x => x = v_fire) univ = {v_fire} := by
    ext x; simp [eq_comm]
  rw [h_filter_eq_single, Finset.sum_singleton]
  have h_filter_eq_erase : Finset.filter (fun x => ¬x = v_fire) univ = Finset.univ.erase v_fire := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_erase, and_true, true_and]
  rw [h_filter_eq_erase]
  rw [← vertex_degree_eq_sum_incident_edges G v_fire]
  simp

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
      simp
    · -- Case 3: Sum of two elements satisfying the property
      intro x y hx_deg_zero hy_deg_zero -- hx_deg_zero: deg x = 0, hy_deg_zero: deg y = 0
      -- Goal: deg (x + y) = 0
      rw [deg.map_add, hx_deg_zero, hy_deg_zero, add_zero]
    · -- Case 4: Negative of an element satisfying the property
      intro x hx_deg_zero -- hx_deg_zero: deg x = 0
      -- Goal: deg (-x) = 0
      rw [deg.map_neg, hx_deg_zero, neg_zero]

  have h_deg_sub_eq_sub_deg : deg (D' - D) = deg D' - deg D := by
    simp [sub_eq_add_neg, deg.map_add, deg.map_neg]

  rw [h_deg_sub_eq_sub_deg] at h_deg_diff_zero
  linarith [h_deg_diff_zero]

-- Define a firing script as a function from vertices to integers
def firing_script (V : Type) := V → ℤ

instance: AddCommGroup (firing_script V) := Pi.addCommGroup

-- Principal divisor associated to a firing script
def prin (G : CFGraph V) : firing_script V →+ CFDiv V :=
  {
    toFun := fun σ v => ∑ u : V, (σ u - σ v) * (num_edges G v u),
    map_zero' := by
      have h (w : V) : (0 : V → ℤ) w = 0 := rfl
      simp [h]
      rfl,
    map_add' := by
      intro σ₁ σ₂
      funext v
      dsimp
      rw [← Finset.sum_add_distrib]
      apply sum_congr rfl
      intro u _
      repeat rw [add_apply]
      ring,
  }

lemma prin_eq_neg_laplacian_map (G : CFGraph V) (σ : firing_script V) :
  prin G σ = -laplacian_map G σ := by
  unfold prin laplacian_map
  funext v
  dsimp
  simp [sub_mul]
  apply sub_eq_sub_iff_sub_eq_sub.mp
  -- change goal to showing that both sides of the equation are equal to 0
  have h : ∑ x : V, σ x * ↑(num_edges G v x) - ∑ u : V, ↑(num_edges G v u) * σ u= 0 := by
    rw [sub_eq_zero.mpr]
    apply sum_congr rfl
    intro u _
    ring
  rw [h,sub_eq_zero.mpr]
  rw [sum_mul]
  apply sum_congr rfl
  intro u _
  ring

lemma principal_iff_eq_prin (G : CFGraph V) (D : CFDiv V) :
  D ∈ principal_divisors G ↔ ∃ σ : firing_script V, D = prin G σ := by
  unfold principal_divisors
  constructor
  · -- Forward direction
    intro h_inp
    -- Use the defining property of a subgroup closure
    refine AddSubgroup.closure_induction h_inp ?_ ?_ ?_ ?_
    . -- Case 1: h_inp is a firing vector
      intro x h_firing
      rcases h_firing with ⟨v, rfl⟩
      let σ : firing_script V := λ u => if u = v then 1 else 0
      use σ
      rw [prin_eq_neg_laplacian_map G σ]
      unfold laplacian_map firing_vector
      funext w
      dsimp [σ]
      by_cases h_eq : w = v
      . -- Case w = v
        simp [h_eq, num_edges_self_eq_zero G v]
      . -- Case w ≠ v
        simp [h_eq, num_edges_symmetric G v w]
    . -- Case 2: h_inp is zero divisor
      use 0
      simp
    . -- Case 3: h_inp is a sum of two principal divisors
      intros x y h_x_prin h_y_prin
      rcases h_x_prin with ⟨σ₁, h_x_eq⟩
      rcases h_y_prin with ⟨σ₂, h_y_eq⟩
      rw [h_x_eq, h_y_eq]
      use σ₁ + σ₂
      simp
    . -- Case 4: h_inp is negation of a principal divisor
      intro x h_x_prin
      rcases h_x_prin with ⟨σ, h_x_eq⟩
      use -σ
      rw [h_x_eq]
      simp
  . -- Backward direction
    intro h_prin
    rcases h_prin with ⟨σ, h_eq⟩
    unfold prin at h_eq
    let D₁ := ∑ u : V, (σ u) • (firing_vector G u)
    have D1_principal :D₁ ∈ principal_divisors G := by
      apply AddSubgroup.sum_mem _ _
      intro u _
      apply AddSubgroup.zsmul_mem _ _
      exact mem_principal_divisors_firing_vector G u
    have D_eq : D₁ = D := by
      rw [h_eq]
      funext v
      -- expand the definition of D₁
      dsimp [D₁]
      unfold firing_vector
      -- Move that v into the sum on the left side
      rw [Finset.sum_apply]
      simp
      have: ∀ (u : V), (σ u - σ v) * ↑(num_edges G v u) = σ u * ↑(num_edges G v u) - σ v * ↑(num_edges G v u) := by intro u; ring
      simp [this]
      rw [← Finset.mul_sum]
      simp [← vertex_degree_eq_sum_num_edges]

      have h (v : V): vertex_degree G v = ∑ x : V, if v = x then vertex_degree G v else 0 := by
        rw [Finset.sum_ite]
        rw [Finset.sum_const_zero,add_zero]
        have : Finset.filter (Eq v) univ = {v} := by
          ext x; simp [eq_comm]
        rw [this, Finset.sum_singleton]
      rw [h v]
      rw [Finset.mul_sum]
      -- Combine the right side into a single sum again
      rw [← Finset.sum_sub_distrib]
      apply sum_congr rfl
      intro u _
      by_cases h_eq : v = u
      · -- Case v = u
        rw [h_eq]
        have : num_edges G u u = 0 := num_edges_self_eq_zero G u
        rw [this]
        simp
      · -- Case v ≠ u
        simp [h_eq]
        left
        rw [num_edges_symmetric G v u]
    rw [← D_eq]
    exact D1_principal


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
    ∃ v ∈ S, D v < ∑ w in (univ.filter (λ x => x ∉ S)), (num_edges G v w : ℤ))

-- Legal set-firing: Ensure no vertex in S is in debt after firing
def legal_set_firing (G : CFGraph V) (D : CFDiv V) (S : Finset V) : Prop :=
  ∀ v ∈ S, set_firing G D S v ≥ 0

lemma degree_of_firing_vector_is_zero (G : CFGraph V) (v_node : V) :
  deg (firing_vector G v_node) = 0 := by
  unfold deg; simp
  unfold firing_vector
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
    rw [deg.map_add, h_deg_x_zero, h_deg_y_zero, add_zero]
  · -- Case 4: h = -x where deg x = 0
    intros x h_deg_x_zero
    rw [deg.map_neg, h_deg_x_zero, neg_zero]

def q_effective (q : V) (D : CFDiv V) : Prop :=
  ∀ v : V, v ≠ q → D v ≥ 0

structure q_eff_div (V : Type) [DecidableEq V] [Fintype V] [Nonempty V] (q : V):=
  (D : CFDiv V) (h_eff : q_effective q D)


def q_reducer (G : CFGraph V) (q : V) (σ : firing_script V) : Prop :=
  ∀ v : V, σ q ≤ σ v

lemma q_reducer_of_add_princ_reduced (G : CFGraph V) (q : V) (D : CFDiv V) (σ : firing_script V) :
  q_reduced G q (D + prin G σ) → q_effective q D → q_reducer G q σ := by
  intro h_q_reduced h_q_effective v
  unfold q_reduced at h_q_reduced
  rcases h_q_reduced with ⟨h_eff, h_S⟩

  have min_exists := Finset.exists_min_image Finset.univ σ (by use q; simp)
  rcases min_exists with ⟨w, ⟨_,w_argmin⟩⟩
  let S := Finset.univ.filter (σ · = σ w)

  -- Reduce goal to q ∈ S
  have sts : q ∈ S → σ q ≤ σ v := by
    intro q_in_S; dsimp [S] at q_in_S; simp at q_in_S
    linarith [w_argmin v (by simp)]
  apply sts

  -- Show that if q ∉ S then D + pring G σ isn't q-reduced
  contrapose! h_S
  use S

  -- Consider each part of the q-reducedness definition
  -- Show that S ⊆ {v : v ≠ q}
  constructor
  rintro x x_S; simp
  contrapose! h_S
  rw [h_S] at x_S
  exact x_S
  -- Show S is nonempty
  constructor
  use w
  dsimp [S]; simp
  -- Show the outdegree inequality
  rintro x x_S; simp
  have h_σx: σ x = σ w := by dsimp[S] at x_S; simp at x_S; exact x_S
  unfold prin; simp

  rw [← Finset.sum_filter_add_sum_filter_not univ (fun x ↦ x ∉ S)]

  have ineq_Dx : 0 ≤ D x := by
    apply h_q_effective
    contrapose! h_S
    rw [← h_S]
    exact x_S
  -- Show some terms are zero, and bound the others
  refine le_trans ?_ (le_add_of_nonneg_left ineq_Dx)
  refine le_trans ?_ (le_add_of_nonneg_right ?_)
  -- Part 1: bound prin σ using outdegree
  refine Finset.sum_le_sum ?_
  intro t h_t_S
  simp at h_t_S
  have h₁: 1 ≤ σ t - σ x := by
    apply Int.pos_iff_one_le.mp
    apply lt_of_le_of_ne
    linarith [w_argmin t (by simp)]
    contrapose! h_t_S
    dsimp [S]; simp
    linarith
  have h₂ : (0:ℤ) ≤ ↑(num_edges G x t) := by
    have := num_edges_nonneg G x t
    -- This line looks weird, but it's doing something: upcasting from ℕ to ℤ. There's probably a better way to do this.
    linarith
  linarith [Int.mul_le_mul_of_nonneg_right h₁ h₂]

  -- Part 2: show other terms are nonnegative
  refine Finset.sum_nonneg ?_
  intro t h_t_notin_S
  rw [h_σx]
  apply mul_nonneg
  linarith [w_argmin t (by simp)]
  linarith [num_edges_nonneg G x t]

theorem q_reduced_unique (G : CFGraph V) (q : V) (D₁ D₂ : CFDiv V) :
  q_reduced G q D₁ ∧ q_reduced G q D₂ ∧ linear_equiv G D₁ D₂ → D₁ = D₂ := by
  intro ⟨h_qred_1,h_qred_2,h_lequiv⟩
  unfold linear_equiv at h_lequiv
  simp [principal_iff_eq_prin] at h_lequiv
  rcases h_lequiv with ⟨σ, h_D2_eq⟩
  have h_reducer_1 : q_reducer G q σ := by
    apply q_reducer_of_add_princ_reduced G q D₁ σ
    rw [← h_D2_eq]
    simp
    exact h_qred_2
    exact h_qred_1.left
  have h_reducer_2 : q_reducer G q (-σ) := by
    apply q_reducer_of_add_princ_reduced G q D₂ (-σ)
    rw [(prin G).map_neg, ← sub_eq_add_neg]
    simp [← h_D2_eq]
    exact h_qred_1
    exact h_qred_2.left
  have : ∀ v : V, σ v = σ q := by
    intro v
    specialize h_reducer_1 v
    specialize h_reducer_2 v
    repeat rw [Pi.neg_apply] at h_reducer_2
    linarith
  have : prin G σ = (0 : CFDiv V) := by
    funext v
    unfold prin
    dsimp
    simp [this]
  rw [this] at h_D2_eq
  apply sub_eq_zero.mp at h_D2_eq
  rw [h_D2_eq]

def benevolent (G : CFGraph V) (S : Finset V) : Prop :=
  ∀ (D : CFDiv V), ∃ (E : CFDiv V), linear_equiv G D E ∧ (∀ (v : V), E v < 0 → v ∈ S)

lemma benevolent_of_nonempty {G : CFGraph V} (h_conn : graph_connected G) (S : Finset V) (h_nonempty : S.Nonempty) :
  benevolent G S := by
  by_cases h : S = Finset.univ
  · -- Case: S = V
    intro D
    use D
    -- Verify the first part of the conjuction
    constructor
    exact (linear_equiv_is_equivalence G).refl D
    -- Verify second part
    intro v h_neg
    rw [h]
    simp
  · -- Case: S ≠ V
    let h_conn' := h_conn -- Unsimplified copy for later
    dsimp [graph_connected] at h_conn
    specialize h_conn S
    have : ∃ (v w : V), v ∈ S ∧ w ∉ S := by
      let v := Classical.choose h_nonempty
      have v_in_S : v ∈ S := Classical.choose_spec h_nonempty
      have : (univ \ S).Nonempty := by
        contrapose! h
        simp at h
        exact h
      let w := Classical.choose this
      have h_vw : w ∉ S := by
        have := Classical.choose_spec this
        simp at this
        exact this
      use v, w
    have h_vw := h_conn this
    rcases h_vw with ⟨v,h_v,w,h_w,h_edge⟩
    let T := insert w S
    have h_T_nonempty : T.Nonempty := by
      use w
      simp [T]
    have ih := benevolent_of_nonempty h_conn' T h_T_nonempty
    intro D
    specialize ih D
    rcases ih with ⟨E1, h_lequiv_1, h_eff_S⟩
    -- Now need to adjust E1 to get E
    have : ∃ E : CFDiv V, linear_equiv G E1 E ∧ (∀ v : V, E v < 0 → v ∈ S) := by
      let fire := firing_vector G v
      have p_f : fire ∈ principal_divisors G := mem_principal_divisors_firing_vector G v
      let k := max 0 (-(E1 w))
      let E := E1 + k • fire
      use E
      constructor
      · -- Verify linear equivalence
        unfold linear_equiv
        have h_diff : E - E1 = k • fire := by
          simp [E]
        rw [h_diff]
        exact AddSubgroup.zsmul_mem _ p_f k
      · -- Verify effectiveness outside S
        intro x h_E_neg
        by_cases h_x_eq_w : x = w
        · -- Case x = w
          exfalso
          rw [h_x_eq_w] at h_E_neg
          dsimp [E] at h_E_neg
          contrapose! h_E_neg
          simp [k]
          by_cases h : -(E1 w) ≥ 0
          . -- Case : E1 w nonpositive
            have : max 0 (-(E1 w)) = -(E1 w) := by simp [h]
            rw [this]
            have : E1 w + -E1 w * fire w = (-E1 w) * (fire w -1) := by ring
            rw [this]
            apply mul_nonneg h
            -- Goal: fire w -1 ≥ 0
            dsimp [fire, firing_vector]
            have : ¬ (w = v) := by
              contrapose! h_w
              rw [← h_w] at h_v
              exact h_v
            simp [this]
            linarith [h_edge]
          . -- Case : E1 w positive
            simp at h
            dsimp [max]
            have : 0 ≥ -E1 w := by linarith [h]
            simp [this]
            linarith [h]
        . -- Case : x ≠ w
          have h_T := h_eff_S x
          by_contra! x_nin_S
          have h_xT : x ∉ T := by
            contrapose! x_nin_S with x_in_T
            dsimp [T] at x_in_T
            simp [h_x_eq_w] at x_in_T
            exact x_in_T
          specialize h_eff_S x
          contrapose! h_eff_S
          simp [h_xT]
          contrapose! h_E_neg with h_E1
          -- Goal: 0 ≤ E x
          dsimp [E]
          apply add_nonneg h_E1
          -- Goal : 0 ≤ k * fire x
          apply mul_nonneg
          -- Show 0 ≤ k
          dsimp [k]
          simp
          -- Show 0 ≤ fire x
          dsimp [fire, firing_vector]
          have : ¬ (x = v) := by
            contrapose! x_nin_S with x_eq_v
            rw [x_eq_v]
            exact h_v
          simp [this]
    rcases this with ⟨E, h_lequiv_2, h_eff_S_final⟩
    use E
    constructor
    · -- Verify linear equivalence
      exact (linear_equiv_is_equivalence G).trans h_lequiv_1 h_lequiv_2
    · -- Verify effectiveness outside S
      exact h_eff_S_final
termination_by ((univ : Finset V).card - S.card)
decreasing_by
  have h_succ: (insert w S).card = S.card + 1 := by
    apply Finset.card_eq_succ.mpr
    use w, S
  rw [h_succ]
  refine Nat.sub_succ_lt_self univ.card S.card ?_
  have : (insert w S).card ≤ (univ : Finset V).card := by
    apply Finset.card_le_card
    simp
  linarith

lemma q_effective_exists {G : CFGraph V} (h_conn : graph_connected G) (q : V) (D : CFDiv V) :
  ∃ (E : CFDiv V), q_effective q E ∧ linear_equiv G D E := by
  have h_bene := benevolent_of_nonempty h_conn {q} (by use q; simp) D
  rcases h_bene with ⟨E,h_equiv, h_eff⟩
  have : q_effective q E := by
    intro v v_ne_q
    specialize h_eff v
    contrapose! h_eff
    simp [h_eff]
    exact v_ne_q
  exact ⟨E,this, h_equiv⟩

def reduces_to (G : CFGraph V) (q : V) (D₁ D₂: CFDiv V) : Prop :=
  ∃ σ : firing_script V, q_reducer G q σ ∧ D₂ = D₁ + prin G σ

lemma reduces_to_reflexive (G : CFGraph V) (q : V) (D : CFDiv V) :
  reduces_to G q D D := by
  use 0
  constructor
  · -- Show q_reducer holds for the zero firing script
    intro v
    repeat rw [Pi.zero_apply]
  · -- Show D = D + prin G 0
    simp [prin]

lemma reduces_to_transitive (G : CFGraph V) (q : V) (D₁ D₂ D₃ : CFDiv V) :
  reduces_to G q D₁ D₂ → reduces_to G q D₂ D₃ → reduces_to G q D₁ D₃ := by
  intro h_red_12 h_red_23
  rcases h_red_12 with ⟨σ₁, h_reducer_1, h_D2_eq⟩
  rcases h_red_23 with ⟨σ₂, h_reducer_2, h_D3_eq⟩
  use σ₁ + σ₂
  constructor
  · -- Show q_reducer holds for σ₁ + σ₂
    intro v
    repeat rw [Pi.add_apply]
    apply add_le_add (h_reducer_1 v) (h_reducer_2 v)
  · -- Show D₃ = D₁ + prin G (σ₁ + σ₂)
    rw [(prin G).map_add, ← add_assoc]
    rw [← h_D2_eq, ← h_D3_eq]

lemma reduces_to_antisymmetric {G : CFGraph V} (h_conn : graph_connected G) (q : V) (D₁ D₂ : CFDiv V) :
  reduces_to G q D₁ D₂ → reduces_to G q D₂ D₁ → D₁ = D₂ := by
  intro h_red_12 h_red_21
  rcases h_red_12 with ⟨σ₁, h_reducer_1, h_D2_eq⟩
  rcases h_red_21 with ⟨σ₂, h_reducer_2, h_D1_eq⟩
  rw [h_D2_eq, add_assoc, ← (prin G).map_add] at h_D1_eq
  let σ := σ₁ + σ₂
  have h_reducer : q_reducer G q σ := by
    intro v
    apply add_le_add (h_reducer_1 v) (h_reducer_2 v)
  have prin_sum_zero : prin G (σ) = 0 := by
    simp at h_D1_eq
    rw [← (prin G).map_add] at h_D1_eq
    exact h_D1_eq
  let S := Finset.univ.filter (λ v => σ v = σ q)
  have q_in_S : q ∈ S := by
    dsimp [S]
    simp
  have S_full : ∀ v : V, v ∈ S := by
    by_contra! v_nin_S
    rcases v_nin_S with ⟨v, h_v⟩
    have h : ∃ (u v : V), u ∈ S ∧ v ∉ S := by
      use q, v
    have := h_conn S h
    rcases this with ⟨u, h_u_in_S, w, h_w_nin_S, h_edge⟩
    have zero_eq: (prin G) σ u = 0 := by
      simp [prin_sum_zero]
    dsimp [prin] at zero_eq

    have nonneg_terms: ∀ w : V, (σ w - σ u) * (num_edges G u w : ℤ) ≥ 0 := by
      intro w
      have h_σw_ge_σu : σ w - σ u ≥ 0 := by
        dsimp [S] at h_u_in_S h_w_nin_S
        simp at h_u_in_S
        specialize h_reducer w
        linarith
      have h_num_edges_nonneg : (num_edges G u w : ℤ) ≥ 0 := by
        have := num_edges_nonneg G u w
        linarith
      apply Int.mul_nonneg h_σw_ge_σu h_num_edges_nonneg
    have pos_term : ∃ (w : V), (σ w - σ u) * (num_edges G u w : ℤ) > 0 := by
      use w
      apply Int.mul_pos
      · -- Show σ w - σ u > 0
        dsimp [S] at h_u_in_S h_w_nin_S
        simp at h_u_in_S h_w_nin_S
        specialize h_reducer w
        rw [h_u_in_S]
        apply lt_of_le_of_ne at h_reducer
        have : ¬ σ q = σ w := by
          contrapose! h_w_nin_S
          rw [← h_w_nin_S]
        apply h_reducer at this
        linarith
      · -- Show num_edges G u w > 0
        simp [h_edge]
    have : ∑ u_1 : V, (σ u_1 - σ u) * ↑(num_edges G u u_1) >0 := by
      apply Finset.sum_pos'
      intro i _
      exact nonneg_terms i
      rcases pos_term with ⟨w, h_pos⟩
      use w
      simp
      exact h_pos
    linarith [zero_eq]
  simp [S] at S_full
  have : ∀ v : V, σ₁ v = σ₁ q := by
    intro v
    specialize h_reducer_1 v
    specialize h_reducer_2 v
    specialize S_full v
    dsimp [σ] at S_full
    repeat rw [_root_.add_apply] at S_full
    linarith
  have : prin G σ₁ = 0 := by
    funext v
    unfold prin
    dsimp
    simp [this]
  rw [this] at h_D2_eq
  rw [h_D2_eq]
  simp

-- A vertex is called ``dormant'' if it can never be fired in a firing script from D to a q-effective divisor.
def active (G : CFGraph V) (q : V) (D : CFDiv V) (v : V) : Prop :=
  ∃ σ : firing_script V, q_reducer G q σ ∧ q_effective q (D + prin G σ) ∧ σ q < σ v

lemma q_reduced_of_no_active (G :CFGraph V) {q : V} {D : CFDiv V} (h_eff : q_effective q D) (h_no_active : ∀ v : V, ¬ active G q D v) :
  q_reduced G q D := by
  contrapose! h_no_active with h_not_q_reduced
  dsimp [q_reduced] at h_not_q_reduced
  push_neg at h_not_q_reduced
  rcases h_not_q_reduced h_eff with ⟨S, h_S_subset, h_S_nonempty, h_outdeg⟩
  have q_nin_S : q ∉ S := by
    intro h_contra
    have := h_S_subset h_contra
    simp at this
  -- Construct a firing script that fires all vertices in S
  let σ : firing_script V := λ v => if v ∈ S then 1 else 0
  have h_reducer : q_reducer G q σ := by
    intro v
    dsimp [σ]
    simp [q_nin_S]
    by_cases h : v ∈ S
    simp [h]; simp [h]
  use Classical.choose h_S_nonempty
  let h := Classical.choose_spec h_S_nonempty
  dsimp [active]
  use σ
  constructor
  exact h_reducer
  dsimp [σ]
  simp [h, q_nin_S]
  -- Show q_effective holds
  intro x x_ne_q
  dsimp [prin]
  by_cases h_x : x ∈ S
  · -- Case: x ∈ S
    simp [h_x]
    have simp_ite : ∀ x_1 : V, ((if x_1 ∈ S then 1 else 0) - 1) = -(if x_1 ∈ S then 0 else 1) := by
      intro x_1
      by_cases h_x1 : x_1 ∈ S
      simp [h_x1]
      simp [h_x1]
    suffices (∑ x_1 : V, if x_1 ∈ S then 0 else ↑(num_edges G x x_1)) ≤ D x by
      simp [simp_ite,this]
    specialize h_outdeg x h_x
    have : (∑ w ∈ Finset.filter (fun x ↦ x ∉ S) univ, ↑(num_edges G x w) : ℤ) = (∑ x_1 : V, if x_1 ∈ S then 0 else ↑(num_edges G x x_1)) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y _
      simp
    rw [this] at h_outdeg
    exact h_outdeg
  · -- Case: x ∉ S
    simp [h_x]
    have : 0 ≤ D x := by
      apply h_eff
      exact x_ne_q
    apply add_nonneg (this)
    apply Finset.sum_nonneg
    intro w _
    simp

noncomputable def reduction_excess (G : CFGraph V) (q : V) (D : CFDiv V) : ℤ := by
  classical
  exact (∑ v : V, if active G q D v then D v else 0)


lemma reduction_excess_nonneg (G : CFGraph V) {q : V} {D : CFDiv V} (h_eff : q_effective q D) :
  0 ≤ reduction_excess G q D := by
  dsimp [reduction_excess]
  apply Finset.sum_nonneg
  intro v _
  dsimp
  by_cases h_active : active G q D v
  · -- Case: v is active
    simp [h_active]
    apply h_eff
    intro h_contra
    rw [h_contra] at h_active
    dsimp [active] at h_active
    rcases h_active with ⟨σ, h_reducer, h_eff', h_ineq⟩
    simp at h_ineq
  · -- Case: v is not active
    simp [h_active]

theorem q_effective_to_q_reduced {G : CFGraph V} (h_conn : graph_connected G) {q : V} {D : CFDiv V} (h_eff : q_effective q D) :
  ∃ E : CFDiv V, q_reduced G q E ∧ linear_equiv G D E := by
  -- Use induction on reduction_excess
  classical -- In order to filter using the undecidable "active"
  let S := Finset.univ.filter (λ v : V => active G q D v)
  have q_nin_S : q ∉ S := by
    intro h_contra
    dsimp [S] at h_contra
    simp at h_contra
    dsimp [active] at h_contra
    rcases h_contra with ⟨σ, h_reducer, h_ineq⟩
    simp at h_ineq
  by_cases h_S_empty : S = ∅
  · -- Case: No active vertices, so D is already q-reduced
    use D
    constructor
    · -- q-reducedness
      apply q_reduced_of_no_active G h_eff
      intro v h_contra
      have : v ∈ S := by
        dsimp [S]
        simp [h_contra]
      rw [h_S_empty] at this
      -- "this" is not v ∈ ∅, a contradiction
      simp at this
    . -- Linear equivalence
      exact (linear_equiv_is_equivalence G).refl D
  · -- Case: There are active vertices. Choose one on the boundary.
    have : ∃ v : V, active G q D v := by
      contrapose! h_S_empty with h_no_active
      dsimp [S]
      simp [h_no_active]
    rcases this with ⟨v_active, h_v_active⟩
    have : ∃ (v q : V), v ∈ S ∧ q ∉ S := by
      use v_active, q
      simp [q_nin_S]
      simp [S]
      exact h_v_active
    have := h_conn S this
    rcases this with ⟨v, v_in_S, w, w_nin_S, h_edge⟩
    -- Fire involving v to get a new divisor D'
    simp [S] at v_in_S
    dsimp [active] at v_in_S
    rcases v_in_S with ⟨σ, h_reducer, h_eff_S, h_ineq⟩
    let D' := D + prin G (σ)
    have D_equiv_D' : linear_equiv G D D' := by
      unfold linear_equiv
      have : D' - D = prin G σ := by
        simp [D']
      rw [this]
      apply (principal_iff_eq_prin G (prin G σ)).mpr ⟨σ,rfl⟩

    -- Facts about D', needed for induction
    have h_eff' : q_effective q D' := by
      intro x x_ne_q
      dsimp [D']
      exact h_eff_S x x_ne_q

    have h_active_shrinks (x : V): active G q D' x → active G q D x := by
      intro h_active_D'
      dsimp [active]
      rcases h_active_D' with ⟨σ', h_reducer', h_eff'', h_ineq'⟩
      use σ + σ'
      constructor
      · -- Show q_reducer
        intro y
        repeat rw [Pi.add_apply]
        apply add_le_add (h_reducer y) (h_reducer' y)
      constructor
      · -- Show q_effective
        intro z z_ne_q
        dsimp [D'] at h_eff''
        specialize h_eff'' z z_ne_q
        rw [(prin G).map_add, ← add_assoc]
        exact h_eff''
      · -- Show chips are fired from x
        repeat rw [Pi.add_apply]
        apply add_lt_add_of_le_of_lt
        exact h_reducer x
        exact h_ineq'

    have chips_to_inactive_per_edge (u x : V) : ¬ active G q D x → (σ u - σ x) * ↑(num_edges G x u) ≥ 0 := by
      intro h_inactive_D
      dsimp [D']
      simp
      apply mul_nonneg
      · -- Show σ u - σ x ≥ 0
        have : σ x ≤ σ q := by
          dsimp [active] at h_inactive_D
          push_neg at h_inactive_D
          specialize h_inactive_D σ
          exact h_inactive_D h_reducer h_eff'
        have : σ u ≥ σ q := by
          specialize h_reducer u
          linarith
        linarith
      · -- Show num_edges G x u ≥ 0
        simp [num_edges_nonneg G x u]

    have chips_to_inactive (x : V) : ¬ active G q D x → D x ≤ D' x := by
      -- Goal: 0 ≤ ∑ (σ u - σ x) * num_edges G x u
      intro h_inactive_D
      dsimp [D', prin]
      simp
      apply Finset.sum_nonneg
      intro u _
      exact chips_to_inactive_per_edge u x h_inactive_D

    have h_smaller : reduction_excess G q D' < reduction_excess G q D := by
      dsimp [reduction_excess]
      repeat rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      -- First, pass to a sum over non-active vertices
      have h (D : CFDiv V) : ∑ x ∈ Finset.filter (active G q D) univ, D x = deg D - ∑ x ∈ Finset.filter (fun v => ¬ active G q D v) univ, D x := by
        dsimp [deg]
        rw [← Finset.sum_filter_add_sum_filter_not univ (fun v => active G q D v)]
        simp
      rw [h D', h D]
      have : deg D = deg D' :=
        linear_equiv_preserves_deg G D D' D_equiv_D'
      rw [← this]
      simp
      -- Write as a sum over all vertices in order to compare terms
      have h (D : CFDiv V) : ∑ x ∈ Finset.filter (fun v => ¬ active G q D v) univ, D x = ∑ x : V, if ¬ active G q D x then D x else 0 := by
        rw [Finset.sum_filter]
      rw [h D', h D]
      -- Now compare term-by-term
      apply Finset.sum_lt_sum
      -- Show each term is ≤ the corresponding term
      intro x _
      by_cases h_active_D' : active G q D' x
      · -- Case: x is active in D'. Then already active in D.
        have h_active_D := h_active_shrinks x h_active_D'
        simp [h_active_D, h_active_D']
      · -- Case: x is not active in D'.
        simp [h_active_D']
        by_cases h_active_D : active G q D x
        · -- Subcase: x is active in D
          simp [h_active_D]
          -- Show 0 ≤ D' x
          apply h_eff' x
          intro h_contra
          rw [h_contra] at h_active_D
          dsimp [S] at q_nin_S
          simp at q_nin_S
          contradiction
        · -- Subcase: x is not active in D either
          simp [h_active_D]
          -- Show D x ≤ D' x
          exact chips_to_inactive x h_active_D
      -- Now, show that strict inequality holds for at least one term
      use w
      have h_inactive_D : ¬ active G q D w := by
        dsimp [S] at w_nin_S
        simp at w_nin_S
        exact w_nin_S
      have h_active_D' : ¬ active G q D' w := by
        contrapose! h_inactive_D with h_active_D'
        exact (h_active_shrinks w) h_active_D'
      simp [h_inactive_D, h_active_D']
      -- Show D w < D' w
      dsimp [D', prin]
      simp
      -- Goal: 0 < ∑ (σ u - σ w) * num_edges
      apply Finset.sum_pos'
      -- Show each term is nonnegative
      intro u _
      exact chips_to_inactive_per_edge u w h_inactive_D
      -- Show at least one term is positive
      use v
      simp
      -- Goal: (σ v - σ w) * num_edges G w v > 0
      apply Int.mul_pos
      · -- Show σ v - σ w > 0
        have : σ w ≤ σ q := by
          dsimp [active] at h_inactive_D
          push_neg at h_inactive_D
          specialize h_inactive_D σ
          exact h_inactive_D h_reducer h_eff'
        linarith [this, h_ineq]
      . -- Show num_edges G w v > 0
        rw [← num_edges_symmetric G v w]
        simp [h_edge]
    have ih := q_effective_to_q_reduced h_conn h_eff'
    rcases ih with ⟨E, h_q_reduced, h_lequiv⟩
    use E
    constructor
    · -- q-reducedness
      exact h_q_reduced
    · -- Linear equivalence
      refine (linear_equiv_is_equivalence G).trans ?_ h_lequiv
      exact D_equiv_D'
termination_by (reduction_excess G q D).toNat
decreasing_by
  -- Some effort needed to deal with ℤ versus ℕ
  rw [Int.toNat_lt]
  simp [reduction_excess_nonneg]
  dsimp [D'] at h_smaller
  left
  exact h_smaller
  exact reduction_excess_nonneg G h_eff'

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
      simp only [if_pos h_head, add_comm, Multiset.card_singleton, Multiset.card_eq_one]
      obtain ⟨e,f⟩ := e_head
      rcases h_head with h_left  | h_right
      -- Subcase: e = v
      have e_eq_v : e =v  := h_left
      have f_neq_v : f ≠ v := by
        contrapose! h_left
        simp [h_left]
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
        simp [h_right]
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
      simp [h_head]
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
