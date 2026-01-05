import Mathlib.Tactic

import Init.Core
import Init.NotationExtra

import Paperproof

set_option linter.unusedVariables false
set_option trace.split.failure true
set_option linter.unusedSectionVars false

open Multiset Finset

/-!
## Chip-firing graphs and their main attributes.
-/

-- Assume V is a finite type with decidable equality
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]

/-- An edge set is *loopless* if it does not contain (v,v). -/
def isLoopless (edges : Multiset (V × V)) : Prop :=
  ∀ v, (v, v) ∉ edges

/-- A *chip-firing graph* is a loopless multigraph.
It is not assumed connected by default, though many of our main theorems pertain to connected graphs. -/
structure CFGraph (V : Type) [DecidableEq V] [Fintype V] [Nonempty V] where
  (edges : Multiset (V × V))
  (loopless : isLoopless edges)

/-- The number of edges between vertex v and vertex w. When working with chip-firing graphs in this repository, it is usually preferable to work with this function, rather than with the multiset of edges directly. -/
def num_edges (G : CFGraph V) (v w : V) : ℕ :=
  Multiset.card (G.edges.filter (λ e => e = (v, w) ∨ e = (w, v)))

/-- A graph is *connected* if the vertices cannot be partitioned into two nonempty sets with no edges between them. This is equivalent to saying there is a path between any two vertices, but the first definition is more convenient to work with in this repository. -/
def graph_connected (G : CFGraph V) : Prop :=
  ∀ S : Finset V, (∃ (v w : V), v ∈ S ∧ w ∉ S) →
    (∃ v ∈ S, ∃ w ∉ S, num_edges G v w > 0)

/-- The genus of a graph is its cycle rank: |E| - |V| + 1 -/
def genus (G : CFGraph V) : ℤ :=
  Multiset.card G.edges - Fintype.card V + 1

/-- Number of edges between two vertices is non-negative. -/
lemma num_edges_nonneg (G : CFGraph V) (v w : V) :
  num_edges G v w ≥ 0 := by
  exact Nat.zero_le (num_edges G v w)

/-- Number of edges is symmetric -/
lemma num_edges_symmetric (G : CFGraph V) (v w : V) :
  num_edges G v w = num_edges G w v := by
  unfold num_edges
  simp [Or.comm]

/-- Numerical version of *loopless*: num_edges v v = 0. -/
@[simp] lemma num_edges_self_zero (G : CFGraph V) (v : V) :
  num_edges G v v = 0 := by
  unfold num_edges
  rw [Multiset.card_eq_zero]
  apply Multiset.filter_eq_nil.mpr
  intro a h_inE h_eq_loop
  rw [or_self] at h_eq_loop
  rw [h_eq_loop] at h_inE
  exact G.loopless v h_inE

/-- Degree (valence) of a vertex as an integer (defined as the sum of incident edge multiplicities) -/
def vertex_degree (G : CFGraph V) (v : V) : ℤ :=
  ∑ u : V, (num_edges G v u : ℤ)

/-- Vertex degree is non-negative -/
lemma vertex_degree_nonneg (G : CFGraph V) (v : V) :
  vertex_degree G v ≥ 0 := by
  unfold vertex_degree
  apply Finset.sum_nonneg
  intro u _
  exact Int.natCast_nonneg _

/-!
## The divisor group on a chip-firing graph
-/

/-- A *divisor* is a function from vertices to integers. -/
def CFDiv (V : Type) := V → ℤ

/-- CFDiv V forms an Additive Commutative Group. -/
instance : AddCommGroup (CFDiv V) := Pi.addCommGroup

/-- A divisor with one chip at a specified vertex `v_chip` and zero chips elsewhere. -/
def one_chip (v_chip : V) : CFDiv V :=
  fun v => if v = v_chip then 1 else 0

-- Canonical simplications for evaluations of one_chip.
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

lemma add_sub_distrib (D₁ D₂ D₃ : CFDiv V) :
  (D₁ + D₂) - D₃ = (D₁ - D₃) + D₂ := by
  funext x
  simp [sub_apply, add_apply]
  ring

@[simp] lemma smul_apply (n : ℤ) (D : CFDiv V) (v : V) :
  (n • D) v = n * (D v) := by
  rfl

/-- Firing move at a vertex -/
def firing_move (G : CFGraph V) (D : CFDiv V) (v : V) : CFDiv V :=
  λ w => if w = v then D v - vertex_degree G v else D w + num_edges G v w

/-- Borrowing move at a vertex -/
def borrowing_move (G : CFGraph V) (D : CFDiv V) (v : V) : CFDiv V :=
  λ w => if w = v then D v + vertex_degree G v else D w - num_edges G v w

/-- Result of firing a set S on a vertex D -/
def set_firing (G : CFGraph V) (D : CFDiv V) (S : Finset V) : CFDiv V :=
  λ w => D w + ∑ (v ∈ S), (if w = v then -vertex_degree G v else num_edges G v w)

/-- The principal divisor associated to firing a single vertex -/
def firing_vector (G : CFGraph V) (v : V) : CFDiv V :=
  λ w => if w = v then -vertex_degree G v else num_edges G v w

/-- Applying a firing move is equivalent to adding the firing vector. -/
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

/-- The firing vector for a set of vertices -/
def set_firing_vector (G : CFGraph V) (D : CFDiv V) (S : Finset V) : CFDiv V :=
  λ w => ∑ (v ∈ S), (if w = v then -vertex_degree G v else num_edges G v w)

/-- Set firing equals adding the set firing vector. -/
lemma set_firing_eq_add_set_firing_vector (G : CFGraph V) (D : CFDiv V) (S : Finset V) :
  set_firing G D S = D + set_firing_vector G D S := by
  unfold set_firing set_firing_vector
  funext w
  dsimp

/-!
## Principal divisors and linear equivalence
-/

/-- The subgroup of principal divisors is generated by firing vectors at individual vertices. -/
def principal_divisors (G : CFGraph V) : AddSubgroup (CFDiv V) :=
  AddSubgroup.closure (Set.range (firing_vector G))

/-- Two divisors are *linearly equivalent* if their difference is a principal divisor. -/
def linear_equiv (G : CFGraph V) (D D' : CFDiv V) : Prop :=
  D' - D ∈ principal_divisors G

/-- Lemma: Principal divisors contain the firing vector at a vertex -/
lemma mem_principal_divisors_firing_vector (G : CFGraph V) (v : V) :
  firing_vector G v ∈ principal_divisors G := by
  apply AddSubgroup.subset_closure
  apply Set.mem_range_self

/-- Linear equivalence is an equivalence relation on Div(G). -/
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
    have h_symm : D - D' = -(D' - D) := by simp [sub_eq_add_neg]
    rw [h_symm]
    exact AddSubgroup.neg_mem _ h

  -- Transitivity
  · intros D D' D'' h1 h2
    unfold linear_equiv at *
    have h_trans : D'' - D = (D'' - D') + (D' - D) := by simp
    rw [h_trans]
    exact AddSubgroup.add_mem _ h2 h1

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

lemma principal_iff_eq_prin (G : CFGraph V) (D : CFDiv V) :
  D ∈ principal_divisors G ↔ ∃ σ : firing_script V, D = prin G σ := by
  unfold principal_divisors
  constructor
  · -- Forward direction
    intro h_inp
    -- Use the defining property of a subgroup closure
    refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ h_inp
    . -- Case 1: h_inp is a firing vector
      intro x h_firing
      rcases h_firing with ⟨v, rfl⟩
      let σ : firing_script V := λ u => if u = v then 1 else 0
      use σ
      unfold firing_vector prin
      funext w
      dsimp [σ]
      by_cases h_eq : w = v
      . -- Case w = v
        simp [h_eq]
        unfold vertex_degree
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro u _
        by_cases h_eq2 : u = v <;> simp [h_eq2]
      . -- Case w ≠ v
        simp [h_eq, num_edges_symmetric G v w]
    . -- Case 2: h_inp is zero divisor
      use 0
      simp
    . -- Case 3: h_inp is a sum of two principal divisors
      intros x y _ _ h_x_prin h_y_prin
      rcases h_x_prin with ⟨σ₁, h_x_eq⟩
      rcases h_y_prin with ⟨σ₂, h_y_eq⟩
      rw [h_x_eq, h_y_eq]
      use σ₁ + σ₂
      simp
    . -- Case 4: h_inp is negation of a principal divisor
      intro x _ h_x_prin
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
      simp only [this]

      have h (x : V) : (if v = x then -(σ x * vertex_degree G x) else σ x * ↑(num_edges G x v) ) = σ x * (↑(num_edges G x v) ) - σ x * ( (if v = x then vertex_degree G x else 0))  := by
        by_cases h : v = x <;> simp [h]

      simp only [h]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      suffices ∑ x : V, σ x * (if v = x then vertex_degree G x else 0) = ∑ x : V, (σ v * ↑(num_edges G v x)) by
        rw [this]
        simp [num_edges_symmetric]

      dsimp [vertex_degree]
      rw [← Finset.mul_sum]
      simp
    rw [← D_eq]
    exact D1_principal

/-!
## Effective divisors and the ≤ relation on divisors
-/

/-- Divisors form a poset, where D₁ ≤ D₂ means that for all vertices v, D₁(v) ≤ D₂(v). -/
instance : PartialOrder (CFDiv V) := Pi.partialOrder

/-- A divisor is *effective* if it assigns a nonnegative integer to every vertex. Equivalently, it is ≥ 0.-/
def effective (D : CFDiv V) : Prop :=
  ∀ v : V, D v ≥ 0


/-- The submonoid of Effective divisors is denoted Eff V. -/
def Eff (V : Type) [DecidableEq V] [Fintype V] [Nonempty V] : AddSubmonoid (CFDiv V) :=
  { carrier := {D : CFDiv V | effective D},
    zero_mem' := by
      intro v
      simp,
    add_mem' := by
      intros D₁ D₂ h_eff1 h_eff2 v
      specialize h_eff1 v
      specialize h_eff2 v
      simp [add_apply]
      linarith }

@[simp] lemma mem_Eff {D : CFDiv V} : D ∈ Eff V ↔ effective D := Iff.rfl

/-- A one-chip divisor is effective. -/
def eff_one_chip (v : V) : effective (one_chip v) := by
  intro w
  dsimp [one_chip]
  by_cases h_eq : w = v <;> simp [h_eq]

/-- D is effective iff D ≥ 0. -/
lemma eff_iff_geq_zero (D : CFDiv V) : effective D ↔ D ≥ 0:= by
  rfl

/-- D₁ - D₂ is effective iff D₁ ≥ D₂. -/
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

/-- A divisor is winnable if it is linearly equivalent to an effective divisor. -/
def winnable (G : CFGraph V) (D : CFDiv V) : Prop :=
  ∃ D' ∈ Eff V, linear_equiv G D D'


/-!
## The degree homomorphism
-/

/-- Degree of a divisor is the sum of its values at all vertices. -/
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

/-- Effective divisors have nonnegative degree. -/
lemma deg_of_eff_nonneg (D : CFDiv V) :
  effective D → deg D ≥ 0 := by
  intro h_eff
  refine Finset.sum_nonneg ?_
  intro v _
  specialize h_eff v
  exact h_eff

/-- The only effective divisor of degree 0 is 0. -/
lemma eff_degree_zero (D : CFDiv V) : effective D → deg D = 0 → D = 0 := by
  intro h_eff h_deg
  have h_sum : ∑ (v : V), D v = ∑ (v : V), 0 := by
    simp
    apply h_deg
  have h_ineq : ∀ (v : V), D v ≥ 0 := by
    dsimp [effective] at h_eff
    exact h_eff
  funext v; simp
  suffices 0 = D v by apply Eq.symm this
  contrapose! h_sum with h_neq
  have : 0 < D v := lt_of_le_of_ne (h_ineq v) h_neq
  have : ∑ v : V, D v > ∑ v : V, 0 := by
    apply Finset.sum_lt_sum
    simp [h_ineq]
    use v
    simp [this]
  linarith

/-- The degree of a firing vector is zero. -/
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
  dsimp [vertex_degree]
  simp

lemma degree_of_principal_divisor_is_zero (G : CFGraph V) (h : CFDiv V) :
  h ∈ principal_divisors G → deg h = 0 := by
  intro h_mem_princ
  -- principal_divisors is AddSubgroup.closure (Set.range (firing_vector G))
  -- Use induction on the structure of the subgroup
  refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ h_mem_princ
  · -- Case 1: h is in the range of firing_vector G
    intro x hx_in_range
    rcases hx_in_range with ⟨v, rfl⟩
    exact deg_firing_vector_eq_zero G v
  · -- Case 2: h = 0 (the zero divisor)
    simp [deg]
  · -- Case 3: h = x + y where deg x = 0 and deg y = 0
    intros x y _ _ h_x_prin h_y_prin
    rw [deg.map_add, h_x_prin, h_y_prin, add_zero]
  · -- Case 4: h = -x where deg x = 0
    intros x _ h_x_prin
    rw [deg.map_neg, h_x_prin, neg_zero]

/-- Linearly equivalent divisors have the same degree. -/
theorem linear_equiv_preserves_deg (G : CFGraph V) (D D' : CFDiv V) (h_equiv : linear_equiv G D D') :
  deg D = deg D' := by
  unfold linear_equiv at h_equiv
  apply degree_of_principal_divisor_is_zero at h_equiv
  rw [map_sub] at h_equiv
  linarith

lemma helper_divisor_decomposition (G : CFGraph V) (E'' : CFDiv V) (k₁ k₂ : ℕ)
  (h_effective : effective E'') (h_deg : deg E'' = k₁ + k₂) :
  ∃ (E₁ E₂ : CFDiv V),
    effective E₁ ∧ effective E₂ ∧
    deg E₁ = k₁ ∧ deg E₂ = k₂ ∧
    E'' = E₁ + E₂ := by

  let can_split (E : CFDiv V) (a b : ℕ): Prop :=
    ∃ (E₁ E₂ : CFDiv V),
      effective E₁ ∧ effective E₂ ∧
      deg E₁ = a ∧ deg E₂ = b ∧
      E = E₁ + E₂

  let P (a b : ℕ) : Prop := ∀ (E : CFDiv V),
    effective E → deg E = a + b → can_split E a b

  have h_ind (a b : ℕ): P a b := by
    induction' a with a ha
    . -- Base case: a = 0
      intro E h_eff h_deg
      use (0 : CFDiv V), E
      constructor
      -- E₁ is effective
      dsimp [effective]
      intro v
      linarith
      -- E₂ is effective
      constructor
      exact h_eff
      -- deg E₁ = 0
      constructor
      simp
      -- deg E₂ = b
      constructor
      rw[h_deg]
      simp
      -- E = 0 + E
      simp
    . -- Inductive step: assume P a b holds, prove P (a+1) b
      dsimp [P] at *
      intro E E_effective E_deg
      have ex_v : ∃ (v : V), E v ≥ 1 := by
        by_contra h_contra
        push_neg at h_contra
        have h_sum : deg E = 0 := by
          dsimp [deg, deg]
          refine Finset.sum_eq_zero ?_
          intro v hv
          specialize h_contra v
          have h_nonneg : E v ≥ 0 := by
            specialize E_effective v
            assumption
          linarith
        dsimp [deg] at h_sum
        dsimp [deg] at E_deg
        rw [h_sum] at E_deg
        linarith
      rcases ex_v with ⟨v, hv_ge_one⟩
      let E' := E - one_chip v
      have h_E'_effective : effective E' := by
        intro w
        dsimp [E']
        by_cases hw : w = v
        · rw [hw]
          specialize hv_ge_one
          dsimp [one_chip]
          simp
          linarith
        · specialize E_effective w
          dsimp [one_chip]
          simp [hw]
          linarith
      specialize ha E' h_E'_effective
      have h_deg_E' : deg E' = a + b := by
        dsimp [E']; simp; omega
      apply ha at h_deg_E'
      rcases h_deg_E' with ⟨E₁, E₂, h_E1_eff, h_E2_eff, h_deg_E1, h_deg_E2, h_eq_split⟩
      use E₁ + one_chip v, E₂
      -- Check E₁ + one_chip v is effective
      constructor
      apply (Eff V).add_mem
      -- E₁ is effective
      exact h_E1_eff
      -- one_chip v is effective
      intro w
      dsimp [one_chip]
      simp
      by_cases hw : w = v
      rw [hw]
      simp
      simp [hw]
      -- E₂ is effective
      constructor
      exact h_E2_eff
      -- deg (E₁ + one_chip v) = a + 1
      constructor
      simp
      simp at h_deg_E1 h_deg_E2
      rw [h_deg_E1]
      -- deg E₂ = b
      constructor
      exact h_deg_E2
      -- E = (E₁ + one_chip v) + E₂
      dsimp [E'] at h_eq_split
      rw [add_assoc, add_comm (one_chip v), ← add_assoc, ← h_eq_split]
      abel

  exact h_ind k₁ k₂ E'' h_effective h_deg

open Matrix
variable [Fintype V]

/-- The Laplacian matrix of a CFGraph. -/
def laplacian_matrix (G : CFGraph V) : Matrix V V ℤ :=
  λ i j => if i = j then vertex_degree G i else - (num_edges G i j)

-- Note: The Laplacian matrix L is given by Deg(G) - A, where Deg(G) is the diagonal matrix of degrees and A is the adjacency matrix.
-- This matrix can be used to represent the effect of a firing script on a divisor.

/-- Apply the Laplacian matrix to a firing script, and current divisor to get a new divisor. -/
def apply_laplacian (G : CFGraph V) (σ : firing_script V) (D: CFDiv V) : CFDiv V :=
  fun v => (D v) - (laplacian_matrix G).mulVec σ v

/-!
## q-effective divisors
-/

/-- Call a divisor *q-effective* if it has a nonnegative number of chips at all vertices except possibly q. -/
def q_effective (q : V) (D : CFDiv V) : Prop :=
  ∀ v : V, v ≠ q → D v ≥ 0

/-- A divisor that is q-effective. -/
structure q_eff_div (V : Type) [DecidableEq V] [Fintype V] [Nonempty V] (q : V) where
  (D : CFDiv V) (h_eff : q_effective q D)

/-- A set of vertices is benevolent if it is possible to concentrate all debt on this set. -/
def benevolent (G : CFGraph V) (S : Finset V) : Prop :=
  ∀ (D : CFDiv V), ∃ (E : CFDiv V), linear_equiv G D E ∧ (∀ (v : V), E v < 0 → v ∈ S)

/-- In a connected graph, any nonempty set is benevolent. -/
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
            have : max 0 (-(E1 w)) = -(E1 w) := by
              simp; linarith
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

/-- Every divisor can have its debt concentrated on on vertex, as long as the graph is connected. That is, D is linearly equivalent to a q-effective divisor. -/
theorem q_effective_exists {G : CFGraph V} (h_conn : graph_connected G) (q : V) (D : CFDiv V) :
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


/-!
## The q-reduction poset on q-effective divisors
-/

def q_reducer (G : CFGraph V) (q : V) (σ : firing_script V) : Prop :=
  ∀ v : V, σ q ≤ σ v

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
    rw [(prin G).map_zero]; simp

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

lemma constant_script_of_zero_prin {G : CFGraph V} (h_conn : graph_connected G) (σ : firing_script V) : prin G σ = 0 → ∀ (v w : V), σ v = σ w := by
  intro zero_eq
  let min_exists := Finset.exists_min_image Finset.univ σ (by use Classical.arbitrary V; simp)
  rcases min_exists with ⟨q, ⟨_,h_reducer⟩⟩
  have h_reducer : ∀ v : V, σ q ≤ σ v := by
    intro v; specialize h_reducer v
    simp at h_reducer; exact h_reducer
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
    -- apply zero_eq at u
    have zero_eq_at_u: (prin G) σ u = 0 := by
      simp [zero_eq]
    dsimp [prin] at zero_eq_at_u
    linarith [zero_eq_at_u]
  intro v w
  have eq_q : ∀ v : V, σ v = σ q := by
    intro v; specialize S_full v
    dsimp [S] at S_full; simp at S_full
    exact S_full
  rw [eq_q v, eq_q w]

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

  apply constant_script_of_zero_prin h_conn at prin_sum_zero

  have : ∀ v : V, σ₁ v = σ₁ q := by
    intro v
    specialize h_reducer_1 v
    specialize h_reducer_2 v
    dsimp [σ] at prin_sum_zero
    specialize prin_sum_zero q v
    repeat rw [_root_.add_apply] at prin_sum_zero
    linarith
  have : prin G σ₁ = 0 := by
    funext v
    unfold prin
    dsimp
    simp [this]
  rw [this] at h_D2_eq
  rw [h_D2_eq]
  simp

/-!
## q-reduced divisors
-/

/-- A divisior is q-reduced if it is effective away from q, but firing any vertex set disjoint from q puts some vertex into debt. -/
def q_reduced (G : CFGraph V) (q : V) (D : CFDiv V) : Prop :=
  q_effective q D ∧
  (∀ S : Finset V, S ⊆ (Finset.univ.filter (· ≠ q)) → S.Nonempty →
    ∃ v ∈ S, D v < ∑ w ∈  (univ.filter (λ x => x ∉ S)), (num_edges G v w : ℤ))



/-- Helper lemma: a firing script can be understood as first firing the set where the maximum occurs, and no debt is created at this step unless it will remain at the end. -/
lemma maxset_of_script (G : CFGraph V) (σ : firing_script V) : ∃ S : Finset V, Nonempty S ∧ ∀ v ∈ S, (∀ w : V, σ w ≤ σ v ∧ (w ∈ S → σ w = σ v)) ∧ -(prin G σ v) ≥ ∑ w ∈ (univ.filter (λ x => x ∉ S)), (num_edges G v w : ℤ) := by
  let max_exists := Finset.exists_max_image Finset.univ σ (by use Classical.arbitrary V; simp)
  rcases max_exists with ⟨w, ⟨_,w_argmax⟩⟩
  let S := Finset.univ.filter (σ · = σ w)
  use S
  constructor
  -- Show S is nonempty
  use w; dsimp [S]; simp
  intro x x_in_S
  have h_x : σ x = σ w := by
    dsimp [S] at x_in_S; simp at x_in_S; exact x_in_S

  constructor
  -- Maximality condition
  intro y
  constructor
  · -- Show σ y ≤ σ x
    specialize w_argmax y (by simp)
    rw [h_x]; exact w_argmax
  · -- Show that if y ∈ S, then σ y = σ x
    intro y_in_S
    dsimp [S] at y_in_S; simp at y_in_S
    rw [h_x]; exact y_in_S
  -- Show the outdegree inequality
  unfold prin; simp
  rw [← Finset.sum_neg_distrib]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun x ↦ x ∉ S)]

  have : ∑ x_1 ∈ Finset.filter (fun x ↦ ¬x ∉ S) univ, -((σ x_1 - σ x) * ↑(num_edges G x x_1)) = 0 := by
    apply Finset.sum_eq_zero
    intro y h_y
    have h_y : y ∈ S := by simp at h_y; exact h_y
    have h_σy : σ y = σ x := by
      dsimp [S] at h_y; simp at h_y
      rw [h_x, h_y]
    simp [h_σy]
  rw [this, Int.add_zero]
  apply Finset.sum_le_sum
  intro u h_u_notin_S
  by_cases h : num_edges G x u = 0
  · -- Case: num_edges G x u = 0
    simp [h]
  . -- Case: num_edges G x u ≠ 0
    have h : num_edges G x u > 0 := by
      exact Nat.pos_iff_ne_zero.mpr h
    suffices 1 ≤ σ x - σ u by
      rw [neg_mul_eq_neg_mul]
      simp [h, this]
    suffices 0 < σ x - σ u by
      exact Int.le_of_sub_one_lt this
    dsimp [S] at h_u_notin_S; simp at h_u_notin_S
    rw [h_x]
    specialize w_argmax u (by simp)
    linarith [lt_of_le_of_ne w_argmax h_u_notin_S]

/-- Helper lemma: a q-reduced divisor is only equivalent to a q-effective divisor via a q-reducer, i.e. a script that doesn't fire at q. -/
lemma q_reducer_of_add_princ_reduced (G : CFGraph V) (q : V) (D : CFDiv V) (σ : firing_script V) :
  q_reduced G q (D + prin G σ) → q_effective q D → q_reducer G q σ := by
  intro h_q_reduced h_q_effective v
  unfold q_reduced at h_q_reduced
  have h_eff := h_q_reduced.1
  have h_red := h_q_reduced.2


  rcases (maxset_of_script G (-σ)) with ⟨S, S_nonempty, h_S⟩
  simp at S_nonempty
  rcases S_nonempty with ⟨w,h_w⟩
  specialize h_red S
  have q_S : q ∈ S := by
    contrapose! h_q_effective with q_nin_S
    have : S ⊆ Finset.filter (fun x ↦ x ≠ q) univ := by
      intro x x_in_S
      simp
      contrapose! q_nin_S with x_eq_q
      rw [← x_eq_q]
      exact x_in_S
    specialize h_red this
    have : S.Nonempty := by use w
    specialize h_red this
    rcases h_red with ⟨v, v_in_S, h_debt⟩
    have dv_neg := lt_of_lt_of_le h_debt (h_S v v_in_S).2
    simp at dv_neg
    unfold q_effective; push_neg; use v
    suffices v ≠ q by simp [this, dv_neg]
    contrapose! q_nin_S
    rw [← q_nin_S]; exact v_in_S
  have ineq : (-σ) v ≤ (-σ) q := ((h_S q q_S).1 v).1
  repeat rw [Pi.neg_apply] at ineq
  linarith

/-- Alternative description of q-reduced divisors: maximum q-effective diviors with respect to reduction in a linear equivalence class.. -/
lemma maximum_of_q_reduced (G : CFGraph V) {q : V} {D : CFDiv V} (q_eff : q_effective q D) : q_reduced G q D → ∀ D' : CFDiv V, linear_equiv G D D' → q_effective q D' → reduces_to G q D' D := by
  intro h_q_reduced D' h_lequiv h_eff
  unfold linear_equiv at h_lequiv
  simp [principal_iff_eq_prin] at h_lequiv
  rcases h_lequiv with ⟨σ, D'_eq⟩
  have D'_eq : D' = D + prin G σ := by
    rw [← D'_eq]; simp
  rcases (maxset_of_script G σ) with ⟨S, S_nonempty, h_S⟩
  have q_S : q ∈ S := by
    contrapose! h_q_reduced with q_nin_S
    unfold q_reduced; push_neg
    simp [q_eff]; use S
    constructor
    . -- Show S ⊆ {v : v ≠ q}
      intro x x_in_S
      have : x ≠ q := by
        contrapose! q_nin_S; rw [← q_nin_S]; exact x_in_S
      simp [this]
    constructor
    . -- Show S is nonempty
      simp at S_nonempty; rcases S_nonempty with ⟨v, h_v⟩; use v
    . -- Show the outdegree inequality
      intro v v_in_S
      specialize h_S v v_in_S
      have h := h_S.2
      refine le_trans h ?_
      suffices 0 ≤ (D + prin G σ) v by
        simp at this; linarith
      suffices v ≠ q by
        rw [← D'_eq]; apply h_eff; exact this
      contrapose! q_nin_S; rw [← q_nin_S]; exact v_in_S
  use (-σ)
  constructor
  · -- Show q_reducer holds for -σ
    intro v
    repeat rw [Pi.neg_apply]
    linarith [((h_S q q_S).1 v).1]
  · -- Show D = D' + prin G (-σ)
    rw [map_neg]
    simp [D'_eq]

/-- For connected graphs, the converse is true: if a divisor is q_reduced, then it is maximal in the q-reduction partial order. -/
lemma q_reduced_of_maximal {G : CFGraph V} (h_conn : graph_connected G) {q : V} {D : CFDiv V} (q_eff : q_effective q D) :  (∀ D' : CFDiv V, linear_equiv G D D' → q_effective q D' → reduces_to G q D' D) →  q_reduced G q D := by
  intro h_maximal
  unfold q_reduced
  constructor
  · -- Show q_effective holds
    exact q_eff
  · -- Show the outdegree condition
    intro S h_S_subset h_S_nonempty
    have q_nin_S : q ∉ S := by
      intro h_contra
      have := h_S_subset h_contra
      simp at this
    contrapose! h_maximal with h_reduces
    let σ : firing_script V := λ v => if v ∈ S then 1 else 0
    have h_reducer : q_reducer G q σ := by
      intro v
      dsimp [σ]
      have : q ∉ S := by
        by_contra! h_S
        apply h_S_subset at h_S
        simp at h_S
      simp [this]
      by_cases h : v ∈ S <;> simp [h]
    use D + prin G σ
    constructor
    · -- Show linear equivalence
      unfold linear_equiv; simp
      apply (principal_iff_eq_prin G (prin G σ)).mpr
      use σ
    constructor
    · -- Show q_effective
      intro v v_ne_q
      dsimp [σ, prin]
      by_cases h_v : v ∈ S
      · -- Case: v ∈ S
        simp [h_v]
        rw [← Finset.sum_filter_add_sum_filter_not univ (λ x => x ∈ S)]
        have : ∑ x ∈ Finset.filter (fun x ↦ x ∈ S) univ, ((if x ∈ S then (1:ℤ) else 0) - 1) * ↑(num_edges G v x) = (0 : ℤ) := by
          apply Finset.sum_eq_zero
          intro y h_y
          have h_y_in_S : y ∈ S := by simp at h_y; exact h_y
          simp [h_y_in_S]
        rw [this, zero_add]
        have : ∑  x ∈ Finset.filter (fun x ↦ x ∉ S) univ, ((if x ∈ S then (1:ℤ) else 0) - 1) * ↑(num_edges G v x) = - ∑ x ∈ Finset.filter (fun x ↦ x ∉ S) univ, ↑(num_edges G v x) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro x h_x; simp at h_x; simp [h_x]
        rw [this]
        specialize h_reduces v h_v
        linarith
      . -- Case: v ∉ S
        simp [h_v]
        apply add_nonneg
        exact q_eff v v_ne_q
        apply Finset.sum_nonneg; intro w w_in_S
        simp
    . -- Show ¬ reduces_to
      by_contra! h_reduces
      have h' : reduces_to G q D (D + prin G σ) := by use σ
      have : D = D + prin G σ := by
        exact reduces_to_antisymmetric h_conn q D (D + prin G σ) h' h_reduces
      have prin_zero : prin G σ = 0 := by
        calc
          prin G σ = -D + (D + prin G σ) := by abel
          _ = -D + D := by rw [← this]
          _ = 0 := by abel
      apply constant_script_of_zero_prin h_conn  at prin_zero
      let v := Classical.choose h_S_nonempty
      let h_v := Classical.choose_spec h_S_nonempty
      have v_S : v ∈ S := by exact h_v
      specialize prin_zero v q
      dsimp [σ] at prin_zero
      simp [q_nin_S, v_S] at prin_zero

/-- Lemma: The q-reduced representative of an effective divisor is effective.
    This follows from the fact that the reduction process (like Dhar's algorithm or repeated
    legal firings) preserves effectiveness when starting with an effective divisor. -/
lemma helper_q_reduced_of_effective_is_effective (G : CFGraph V) (q : V) (E E' : CFDiv V) :
  effective E → linear_equiv G E E' → q_reduced G q E' → effective E' := by
  intro h_eff h_equiv h_qred
  dsimp [linear_equiv] at h_equiv
  have  := (principal_iff_eq_prin G (E'-E)).mp h_equiv
  rcases this with ⟨σ, h_prin_eq⟩
  have eq_E' : E' = E + prin G σ := by
    rw [← sub_add_cancel E' E, h_prin_eq,add_comm]
  have h_σ : q_reducer G q σ := by
    apply q_reducer_of_add_princ_reduced G q E σ
    rw [← eq_E']
    exact h_qred
    intro v _
    exact h_eff v
  have h_σ_toward_q : (prin G σ) q ≥ 0 := by
    dsimp [prin]
    apply Finset.sum_nonneg
    intro e _
    apply mul_nonneg
    linarith [h_σ e]
    exact Int.natCast_nonneg _
  intro v
  by_cases hvq : v = q
  rw [hvq,eq_E', _root_.add_apply]
  exact add_nonneg (h_eff q) h_σ_toward_q
  exact h_qred.1 v hvq

lemma effective_of_winnable_and_q_reduced (G : CFGraph V) (q : V) (D : CFDiv V) :
  winnable G D → q_reduced G q D → effective D := by
  intro h_winnable h_qred
  rcases h_winnable with ⟨E, h_eff_E, h_equiv⟩
  have h_equiv' : linear_equiv G E D := by
    exact (linear_equiv_is_equivalence G).symm h_equiv
  exact helper_q_reduced_of_effective_is_effective G q E D h_eff_E h_equiv' h_qred

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



/-- A vertex is called ``active'' if there exists a firing script that leaves the divisor effective away from q, does not fire q, and fires at least once at that vertex. -/
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
        simp

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
  simp
  dsimp [D'] at h_smaller
  left
  exact h_smaller
  exact reduction_excess_nonneg G h_eff'

/- Theorem: Existence of a q-reduced representative within a divisor class -/
theorem exists_q_reduced_representative {G : CFGraph V} (h_conn : graph_connected G) (q : V) (D : CFDiv V) :
  ∃ D' : CFDiv V, linear_equiv G D D' ∧ q_reduced G q D' :=
by
  rcases q_effective_exists h_conn q D with ⟨D_eff, h_eff, h_equiv⟩
  rcases q_effective_to_q_reduced h_conn h_eff with ⟨D_qred, h_qred, h_lequiv'⟩
  use D_qred
  constructor
  · -- Show linear equivalence
    have equiv_rel := linear_equiv_is_equivalence G
    have h_equiv' : linear_equiv G D_eff D_qred := h_lequiv'
    have h_equiv'' : linear_equiv G D D_eff := h_equiv
    exact equiv_rel.trans h_equiv'' h_equiv'
  · -- Show q-reduced property
    exact h_qred

/- Lemma: Every divisor is linearly equivalent to exactly one q-reduced divisor -/
lemma unique_q_reduced {G : CFGraph V} (h_conn : graph_connected G) (q : V) (D : CFDiv V) :
  ∃! D' : CFDiv V, linear_equiv G D D' ∧ q_reduced G q D' := by
  -- Prove existence and uniqueness separately
  have h_exists : ∃ D' : CFDiv V, linear_equiv G D D' ∧ q_reduced G q D' := by
    exact exists_q_reduced_representative h_conn q D

  -- Combine existence and uniqueness using the standard constructor
  obtain ⟨D', hD'⟩ := h_exists
  refine ExistsUnique.intro D' hD' (fun y hy => ?_)
  have h_equiv : linear_equiv G y D' := by
    exact (linear_equiv_is_equivalence G).trans ((linear_equiv_is_equivalence G).symm (hy.1)) (hD'.1)
  exact q_reduced_unique G q y D' ⟨hy.2, hD'.2, h_equiv⟩

/-- Proposition 3.2.4: q-reduced and effective implies winnable -/
theorem winnable_iff_q_reduced_effective {G : CFGraph V} (h_conn : graph_connected G) (q : V) (D : CFDiv V) :
  winnable G D ↔ ∃ D' : CFDiv V, linear_equiv G D D' ∧ q_reduced G q D' ∧ effective D' := by
  constructor
  { -- Forward direction
    intro h_win
    rcases h_win with ⟨E, h_eff, h_equiv⟩
    rcases unique_q_reduced h_conn q D with ⟨D', h_D'⟩
    use D'
    constructor
    · exact h_D'.1.1  -- D is linearly equivalent to D'
    constructor
    · exact h_D'.1.2  -- D' is q-reduced
    · -- Show D' is effective using:
      -- First get E ~ D' by transitivity through D
      have h_equiv_symm : linear_equiv G E D := (linear_equiv_is_equivalence G).symm h_equiv -- E ~ D
      have h_equiv_E_D' : linear_equiv G E D' := (linear_equiv_is_equivalence G).trans h_equiv_symm h_D'.1.1 -- E ~ D ~ D' => E ~ D'
      -- Now use the lemma that q-reduced form of an effective divisor is effective
      exact helper_q_reduced_of_effective_is_effective G q E D' h_eff h_equiv_E_D' h_D'.1.2
  }
  { -- Reverse direction
    intro h
    rcases h with ⟨D', h_equiv, h_qred, h_eff⟩
    use D'
    exact ⟨h_eff, h_equiv⟩
  }
