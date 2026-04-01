import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Matrix.Mul

-- import Paperproof

set_option linter.unusedVariables false
set_option trace.split.failure true
set_option linter.unusedSectionVars false

universe u

open Multiset Finset

/-!
## Chip-firing graphs

A *chip-firing graph* (`CFGraph`) is a loopless undirected multigraph with bundled vertex type
`G.V` (assumed `Fintype`, `DecidableEq`, and `Nonempty`). Edges are stored as a multiset of pairs;
`num_edges G v w` counts total edge multiplicity between `v` and `w`, including both `(v, w)`
and `(w, v)` entries.

We define the *degree* (valence) of a vertex as the sum of edge multiplicities at that vertex,
and the *genus* (cyclomatic number) `g = |E| - |G.V| + 1`, which plays a central role in the
Riemann-Roch theorem for graphs ([Corry-Perkinson], Chapter 5).

Many main theorems in this library require connectivity; see `graph_connected`.
-/

/-- A *chip-firing graph* is a loopless multigraph.
It is not assumed connected by default, though many of our main theorems pertain to connected graphs. -/
structure CFGraph  where
  V : Type u
  [instDecidableEq : DecidableEq V]
  [instFintype : Fintype V]
  [instNonempty : Nonempty V]
  (edges : Multiset (V × V))
  (loopless : ∀ v, (v, v) ∉ edges)

attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty

/-- The number of edges between vertex v and vertex w. When working with chip-firing graphs in this repository, it is usually preferable to work with this function, rather than with the multiset of edges directly. -/
def num_edges (G : CFGraph) (v w : G.V) : ℕ :=
  Multiset.card (G.edges.filter (λ e => e = (v, w) ∨ e = (w, v)))

/-- A graph is *connected* if the vertices cannot be partitioned into two nonempty sets with no edges between them. This is equivalent to saying there is a path between any two vertices, but the first definition is more convenient to work with in this repository. -/
def graph_connected (G : CFGraph) : Prop :=
  ∀ S : Finset G.V, (∃ (v w : G.V), v ∈ S ∧ w ∉ S) →
    (∃ v ∈ S, ∃ w ∉ S, num_edges G v w > 0)

/-- The genus of a graph is its cycle rank: `|E| - |G.V| + 1`. -/
def genus (G : CFGraph) : ℤ :=
  Multiset.card G.edges - Fintype.card G.V + 1

/-- Number of edges between two vertices is non-negative. -/
lemma num_edges_nonneg (G : CFGraph) (v w : G.V) :
  num_edges G v w ≥ 0 := Nat.zero_le _

/-- Number of edges is symmetric -/
lemma num_edges_symmetric (G : CFGraph) (v w : G.V) :
  num_edges G v w = num_edges G w v := by
  simp [num_edges, Or.comm]

/-- Numerical version of *loopless*: num_edges v v = 0. -/
@[simp] lemma num_edges_self_zero (G : CFGraph) (v : G.V) :
  num_edges G v v = 0 := by
  rw [num_edges, Multiset.card_eq_zero]
  refine Multiset.filter_eq_nil.mpr ?_
  intro e h_inE h_eq
  rw [or_self] at h_eq
  rcases e with ⟨a, b⟩
  cases h_eq
  exact G.loopless v h_inE

/-- Degree (valence) of a vertex as an integer (defined as the sum of incident edge multiplicities) -/
def vertex_degree (G : CFGraph) (v : G.V) : ℤ :=
  ∑ u : G.V, (num_edges G v u : ℤ)

/-- Vertex degree is non-negative -/
lemma vertex_degree_nonneg (G : CFGraph) (v : G.V) :
  vertex_degree G v ≥ 0 := by
  exact Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _

/-!
## The divisor group

A *divisor* (`CFDiv G`) is an integer-valued function on the vertices of a chip-firing graph,
representing a distribution of chips (possibly negative, i.e. debt) across vertices.
The divisor group `Div(G) = CFDiv G` is the abelian group `G.V → ℤ` under pointwise addition.
([Corry-Perkinson], Definition 1.3)

This section establishes basic operations on divisors: pointwise arithmetic lemmas, the
*firing move* at a single vertex (lending chips to all neighbors), the *borrowing move*
(the inverse operation), and the generalization to *set firing* ([Corry-Perkinson],
Definitions 1.5–1.6). The *firing vector* `firing_vector G v` is the principal divisor
produced by firing vertex `v` once.
-/

/-- A *divisor* is a function from vertices to integers.
[Corry-Perkinson], Definition 1.3 -/
abbrev CFDiv (G : CFGraph) := G.V → ℤ

/-- A divisor with one chip at a specified vertex `v_chip` and zero chips elsewhere. -/
def one_chip {G : CFGraph} (v_chip : G.V) : CFDiv G :=
  fun v => if v = v_chip then 1 else 0

-- Canonical simplications for evaluations of one_chip.
@[simp] lemma one_chip_apply_v {G : CFGraph} (v : G.V) : one_chip v v = 1 := by
  exact if_pos rfl
@[simp] lemma one_chip_apply_other {G : CFGraph} (v w : G.V) : v ≠ w → one_chip v w = 0 := by
  simp [one_chip]
  intro h
  contrapose! h
  rw [h]
@[simp] lemma one_chip_apply_other' {G : CFGraph} (v w : G.V) : w ≠ v → one_chip v w = 0 := by
  simp [one_chip]


-- Properties of divisor arithmetic
@[simp] lemma add_apply {G : CFGraph} (D₁ D₂ : CFDiv G) (v : G.V) :
  (D₁ + D₂) v = D₁ v + D₂ v := rfl

@[simp] lemma sub_apply {G : CFGraph} (D₁ D₂ : CFDiv G) (v : G.V) :
  (D₁ - D₂) v = D₁ v - D₂ v := rfl

@[simp] lemma zero_apply {G : CFGraph} (v : G.V) :
  (0 : CFDiv G) v = 0 := rfl

@[simp] lemma neg_apply {G : CFGraph} (D : CFDiv G) (v : G.V) :
  (-D) v = -(D v) := rfl

@[simp] lemma distrib_sub_add {G : CFGraph} (D₁ D₂ D₃ : CFDiv G) :
  D₁ - (D₂ + D₃) = (D₁ - D₂) - D₃ := by
  funext; simp; ring

lemma add_sub_distrib {G : CFGraph} (D₁ D₂ D₃ : CFDiv G) :
  (D₁ + D₂) - D₃ = (D₁ - D₃) + D₂ := by
  funext; simp; ring

@[simp] lemma smul_apply {G : CFGraph} (n : ℤ) (D : CFDiv G) (v : G.V) :
  (n • D) v = n * (D v) := rfl

/-- Firing move at a vertex
[Corry-Perkinson], Definition 1.5 -/
def firing_move (G : CFGraph) (D : CFDiv G) (v : G.V) : CFDiv G :=
  λ w => if w = v then D v - vertex_degree G v else D w + num_edges G v w

/-- Borrowing move at a vertex -/
def borrowing_move (G : CFGraph) (D : CFDiv G) (v : G.V) : CFDiv G :=
  λ w => if w = v then D v + vertex_degree G v else D w - num_edges G v w

/-- Result of firing a set S on a vertex D
[Corry-Perkinson], Definition 1.6 -/
def set_firing (G : CFGraph) (D : CFDiv G) (S : Finset G.V) : CFDiv G :=
  λ w => D w + ∑ (v ∈ S), (if w = v then -vertex_degree G v else num_edges G v w)

/-- The principal divisor associated to firing a single vertex -/
def firing_vector (G : CFGraph) (v : G.V) : CFDiv G :=
  λ w => if w = v then -vertex_degree G v else num_edges G v w

/-- Applying a firing move is equivalent to adding the firing vector. -/
lemma firing_move_eq_add_firing_vector (G : CFGraph) (D : CFDiv G) (v : G.V) :
  firing_move G D v = D + firing_vector G v := by
  unfold firing_move firing_vector
  funext w
  by_cases h_eq : w = v
  · simp [h_eq]
    ring
  · simp [h_eq]

/-- The firing vector for a set of vertices -/
def set_firing_vector (G : CFGraph) (D : CFDiv G) (S : Finset G.V) : CFDiv G :=
  λ w => ∑ (v ∈ S), (if w = v then -vertex_degree G v else num_edges G v w)

/-- Set firing equals adding the set firing vector. -/
lemma set_firing_eq_add_set_firing_vector (G : CFGraph) (D : CFDiv G) (S : Finset G.V) :
  set_firing G D S = D + set_firing_vector G D S := by
  unfold set_firing set_firing_vector
  funext w
  dsimp

/-!
## Principal divisors and linear equivalence

A *firing script* (`firing_script G = G.V → ℤ`) assigns an integer firing level to each vertex.
The associated *principal divisor* `prin G σ` records the net chip flow at each vertex when
script `σ` is applied: `(prin G σ)(v) = Σ_u (σ(u) - σ(v)) · num_edges(v, u)`
([Corry-Perkinson], Definition 2.3).

The subgroup of *principal divisors* `principal_divisors G` is generated by the firing vectors
`firing_vector G v` for all `v`. Two divisors `D` and `D'` are *linearly equivalent*
(`linear_equiv G D D'`) if their difference is a principal divisor ([Corry-Perkinson],
Definition 1.8). This defines an equivalence relation on `Div(G)`, and linearly equivalent
divisors have the same degree (see `linear_equiv_preserves_deg`).
-/

/-- The subgroup of principal divisors is generated by firing vectors at individual vertices. -/
def principal_divisors (G : CFGraph) : AddSubgroup (CFDiv G) :=
  AddSubgroup.closure (Set.range (firing_vector G))

/-- Two divisors are *linearly equivalent* if their difference is a principal divisor.
[Corry-Perkinson], Definition 1.8 -/
def linear_equiv (G : CFGraph) (D D' : CFDiv G) : Prop :=
  D' - D ∈ principal_divisors G

/-- Lemma: Principal divisors contain the firing vector at a vertex -/
lemma mem_principal_divisors_firing_vector (G : CFGraph) (v : G.V) :
  firing_vector G v ∈ principal_divisors G := AddSubgroup.subset_closure (Set.mem_range_self v)

/-- Linear equivalence is an equivalence relation on Div(G). -/
theorem linear_equiv_is_equivalence (G : CFGraph) : Equivalence (linear_equiv G) := by
  refine ⟨?_, ?_, ?_⟩
  · intro D
    unfold linear_equiv
    simp
  · intro D D' h
    unfold linear_equiv at *
    simpa [sub_eq_add_neg] using AddSubgroup.neg_mem (principal_divisors G) h
  · intro D D' D'' h1 h2
    unfold linear_equiv at *
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      AddSubgroup.add_mem (principal_divisors G) h2 h1

/-- A *firing script* is an integer-valued function on vertices, recording how many times
each vertex is fired. Negative values represent borrowing. [Corry-Perkinson], Definition 2.2 -/
abbrev firing_script (G : CFGraph) := G.V → ℤ

/-- The group homomorphism sending a firing script `σ` to the principal divisor
`(prin G σ)(v) = Σ_u (σ(u) - σ(v)) * num_edges G v u`.
[Corry-Perkinson], Definition 2.3 (denoted `div(σ)` there) -/
def prin (G : CFGraph) : firing_script G →+ CFDiv G :=
  {
    toFun := fun σ v => ∑ u : G.V, (σ u - σ v) * (num_edges G v u),
    map_zero' := by
      funext v
      simp,
    map_add' := by
      intro σ₁ σ₂
      funext v
      dsimp
      rw [← Finset.sum_add_distrib]
      apply sum_congr rfl
      intro u _
      ring,
  }

/-- A divisor is principal if and only if it equals `prin G σ` for some firing script `σ`.
This gives a concrete characterization of the subgroup `principal_divisors G`. -/
lemma principal_iff_eq_prin (G : CFGraph) (D : CFDiv G) :
  D ∈ principal_divisors G ↔ ∃ σ : firing_script G, D = prin G σ := by
  unfold principal_divisors
  constructor
  · -- Forward direction
    intro h_inp
    -- Use the defining property of a subgroup closure
    refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ h_inp
    . -- Case 1: h_inp is a firing vector
      intro x h_firing
      rcases h_firing with ⟨v, rfl⟩
      let σ : firing_script G := λ u => if u = v then 1 else 0
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
    let D₁ := ∑ u : G.V, (σ u) • (firing_vector G u)
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
      simp only [Finset.sum_apply]
      simp
      have: ∀ (u : G.V), (σ u - σ v) * ↑(num_edges G v u) = σ u * ↑(num_edges G v u) - σ v * ↑(num_edges G v u) := by intro u; ring
      simp only [this]

      have h (x : G.V) : (if v = x then -(σ x * vertex_degree G x) else σ x * ↑(num_edges G x v) ) = σ x * (↑(num_edges G x v) ) - σ x * ( (if v = x then vertex_degree G x else 0))  := by
        by_cases h : v = x <;> simp [h]

      simp only [h]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      suffices ∑ x : G.V, σ x * (if v = x then vertex_degree G x else 0) = ∑ x : G.V, (σ v * ↑(num_edges G v x)) by
        rw [this]
        simp [num_edges_symmetric]

      dsimp [vertex_degree]
      rw [← Finset.mul_sum]
      simp
    rw [← D_eq]
    exact D1_principal

/-!
## Effective divisors and winnability

A divisor is *effective* if it assigns a nonnegative number of chips to every vertex
([Corry-Perkinson], Definition 1.13). The divisor group carries a natural partial order
where `D₁ ≤ D₂` iff `D₁ v ≤ D₂ v` for all `v`; effectivity is equivalent to `D ≥ 0`.
The submonoid of effective divisors is denoted `Eff G`.

A divisor `D` is *winnable* if it is linearly equivalent to some effective divisor
([Corry-Perkinson], Definition 1.14) — that is, the players can collectively win the
dollar game starting from position `D`.
-/

/-- A divisor is *effective* if it assigns a nonnegative integer to every vertex. Equivalently, it is ≥ 0.
[Corry-Perkinson], Definition 1.13 -/
def effective {G : CFGraph} (D : CFDiv G) : Prop :=
  ∀ v : G.V, D v ≥ 0


/-- The submonoid of effective divisors is denoted `Eff G`. -/
def Eff (G : CFGraph) : AddSubmonoid (CFDiv G) :=
  { carrier := {D : CFDiv G | effective D},
    zero_mem' := by
      simp [effective]
    add_mem' := by
      intro D₁ D₂ h_eff1 h_eff2 v
      exact add_nonneg (h_eff1 v) (h_eff2 v) }

@[simp] lemma mem_Eff {G : CFGraph} {D : CFDiv G} : D ∈ Eff G ↔ effective D := Iff.rfl

/-- A one-chip divisor is effective. -/
def eff_one_chip {G : CFGraph} (v : G.V) : effective (one_chip v) := by
  intro w
  dsimp [one_chip]
  by_cases h_eq : w = v <;> simp [h_eq]

/-- D is effective iff D ≥ 0. -/
lemma eff_iff_geq_zero {G : CFGraph} (D : CFDiv G) : effective D ↔ D ≥ 0 := Iff.rfl

/-- D₁ - D₂ is effective iff D₁ ≥ D₂. -/
lemma sub_eff_iff_geq {G : CFGraph} (D₁ D₂ : CFDiv G) : effective (D₁ - D₂) ↔ D₁ ≥ D₂ := by
  rw [eff_iff_geq_zero]
  constructor
  · intro h v
    have := h v
    simp at this ⊢
    linarith
  · intro h v
    have := h v
    simp at this ⊢
    linarith

/-- A divisor is winnable if it is linearly equivalent to an effective divisor.
[Corry-Perkinson], Definition 1.14 -/
def winnable (G : CFGraph) (D : CFDiv G) : Prop :=
  ∃ D' ∈ Eff G, linear_equiv G D D'


/-!
## The degree homomorphism and the Laplacian

The *degree* of a divisor `D` is $\deg(D) = \sum_v D(v)$, the total number of chips
([Corry-Perkinson], Definition 1.4). It is a group homomorphism $\mathrm{Div}(G) \to \mathbb{Z}$.
Principal divisors have degree zero, so linearly equivalent divisors have equal degree
([Corry-Perkinson], Proposition 1.15).

The *Laplacian matrix* `laplacian_matrix G` is the matrix $L = \mathrm{Deg}(G) - A$, where
$\mathrm{Deg}(G)$ is the diagonal degree matrix and $A$ is the adjacency matrix
([Corry-Perkinson], Definition 2.6). Applying the Laplacian to a firing script produces
the corresponding principal divisor.
-/

/-- Degree of a divisor is the sum of its values at all vertices.
[Corry-Perkinson], Definition 1.4 -/
def deg {G : CFGraph} : CFDiv G →+ ℤ := {
  toFun := λ D => ∑ v, D v,
  map_zero' := by
    simp [Finset.sum_const_zero],
  map_add' := by
    intro D₁ D₂
    simp [Finset.sum_add_distrib],
}

@[simp] lemma deg_one_chip {G : CFGraph} (v : G.V) : deg (one_chip v) = 1 := by
  simp [deg, one_chip]

/-- Effective divisors have nonnegative degree. -/
lemma deg_of_eff_nonneg (D : CFDiv G) :
  effective D → deg D ≥ 0 := by
  intro h_eff
  exact Finset.sum_nonneg fun v _ => h_eff v

/-- The only effective divisor of degree 0 is 0. -/
lemma eff_degree_zero (D : CFDiv G) : effective D → deg D = 0 → D = 0 := by
  intro h_eff h_deg
  have h_sum : ∑ (v : G.V), D v = ∑ (v : G.V), 0 := by
    simp
    apply h_deg
  have h_ineq : ∀ (v : G.V), D v ≥ 0 := by
    dsimp [effective] at h_eff
    exact h_eff
  funext v; simp
  suffices 0 = D v by apply Eq.symm this
  contrapose! h_sum with h_neq
  have : 0 < D v := lt_of_le_of_ne (h_ineq v) h_neq
  have : ∑ v : G.V, D v > ∑ v : G.V, 0 := by
    apply Finset.sum_lt_sum
    simp [h_ineq]
    use v
    simp [this]
  linarith

/-- The degree of a firing vector is zero. -/
lemma deg_firing_vector_eq_zero (G : CFGraph) (v_fire : G.V) :
  deg (firing_vector G v_fire) = 0 := by
  dsimp [deg, firing_vector]
  rw [Finset.sum_ite]
  have h_filter_eq_single : Finset.filter (fun x => x = v_fire) univ = {v_fire} := by
    ext x; simp [eq_comm]
  rw [h_filter_eq_single, Finset.sum_singleton]
  have h_filter_eq_erase : Finset.filter (fun x => ¬x = v_fire) univ = Finset.univ.erase v_fire := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_erase, and_true, true_and]
  rw [h_filter_eq_erase]
  simp [vertex_degree]

/-- Every principal divisor has degree zero. -/
lemma degree_of_principal_divisor_is_zero (G : CFGraph) (h : CFDiv G) :
  h ∈ principal_divisors G → deg h = 0 := by
  intro h_mem_princ
  refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ h_mem_princ
  · rintro x ⟨v, rfl⟩
    exact deg_firing_vector_eq_zero G v
  · simp [deg]
  · intro x y _ _ hx hy
    rw [deg.map_add, hx, hy, add_zero]
  · intro x _ hx
    rw [deg.map_neg, hx, neg_zero]

/-- Linearly equivalent divisors have the same degree.
[Corry-Perkinson], Proposition 1.15 -/
theorem linear_equiv_preserves_deg (G : CFGraph) (D D' : CFDiv G) (h_equiv : linear_equiv G D D') :
  deg D = deg D' := by
  unfold linear_equiv at h_equiv
  apply degree_of_principal_divisor_is_zero at h_equiv
  rw [map_sub] at h_equiv
  linarith

/-- An effective divisor of degree `k₁ + k₂` can be decomposed into a sum of two effective
divisors of degrees `k₁` and `k₂` respectively. -/
lemma helper_divisor_decomposition (G : CFGraph) (E'' : CFDiv G) (k₁ k₂ : ℕ)
  (h_effective : effective E'') (h_deg : deg E'' = k₁ + k₂) :
  ∃ (E₁ E₂ : CFDiv G),
    effective E₁ ∧ effective E₂ ∧
    deg E₁ = k₁ ∧ deg E₂ = k₂ ∧
    E'' = E₁ + E₂ := by

  let can_split (E : CFDiv G) (a b : ℕ): Prop :=
    ∃ (E₁ E₂ : CFDiv G),
      effective E₁ ∧ effective E₂ ∧
      deg E₁ = a ∧ deg E₂ = b ∧
      E = E₁ + E₂

  let P (a b : ℕ) : Prop := ∀ (E : CFDiv G),
    effective E → deg E = a + b → can_split E a b

  have h_ind (a b : ℕ): P a b := by
    induction a with
    | zero =>
    . -- Base case: a = 0
      intro E h_eff h_deg
      use (0 : CFDiv G), E
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
    | succ a ha =>
    . -- Inductive step: assume P a b holds, prove P (a+1) b
      dsimp [P] at *
      intro E E_effective E_deg
      have ex_v : ∃ (v : G.V), E v ≥ 1 := by
        by_contra h_contra
        push Not at h_contra
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
      apply (Eff G).add_mem
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

/-- The Laplacian matrix of a CFGraph.
[Corry-Perkinson], Definition 2.6 -/
def laplacian_matrix (G : CFGraph) : Matrix G.V G.V ℤ :=
  λ i j => if i = j then vertex_degree G i else - (num_edges G i j)

-- Note: The Laplacian matrix L is given by Deg(G) - A, where Deg(G) is the diagonal matrix of degrees and A is the adjacency matrix.
-- This matrix can be used to represent the effect of a firing script on a divisor.

/-- Apply the Laplacian matrix to a firing script, and current divisor to get a new divisor. -/
def apply_laplacian (G : CFGraph) (σ : firing_script G) (D: CFDiv G) : CFDiv G :=
  fun v => (D v) - (laplacian_matrix G).mulVec σ v

/-!
## q-effective divisors

Fix a vertex $q$. A divisor $D$ is *$q$-effective* if $D(v) \geq 0$ for all $v \neq q$;
it may have an arbitrary (possibly negative) value at $q$ itself. The structure `q_eff_div`
packages such a divisor with its proof of $q$-effectivity.

A key fact for connected graphs is that every divisor is linearly equivalent to a
$q$-effective divisor (`q_effective_exists`). The proof goes via the notion of a
*benevolent* set: a set $S$ is benevolent if any divisor can be made to have all its
debt concentrated on $S$ via firing moves.
-/

/-- Call a divisor *q-effective* if it has a nonnegative number of chips at all vertices except possibly q. -/
def q_effective {G : CFGraph} (q : G.V) (D : CFDiv G) : Prop :=
  ∀ v : G.V, v ≠ q → D v ≥ 0

/-- A divisor that is q-effective. -/
structure q_eff_div (G : CFGraph) (q : G.V) where
  (D : CFDiv G) (h_eff : q_effective q D)

/-- A set of vertices is benevolent if it is possible to concentrate all debt on this set. -/
def benevolent (G : CFGraph) (S : Finset G.V) : Prop :=
  ∀ (D : CFDiv G), ∃ (E : CFDiv G), linear_equiv G D E ∧ (∀ (v : G.V), E v < 0 → v ∈ S)

/-- In a connected graph, any nonempty set is benevolent. -/
lemma benevolent_of_nonempty {G : CFGraph} (h_conn : graph_connected G) (S : Finset G.V) (h_nonempty : S.Nonempty) :
  benevolent G S := by
  by_cases h : S = Finset.univ
  · -- Case: S = G.V
    intro D
    use D
    -- Verify the first part of the conjuction
    constructor
    exact (linear_equiv_is_equivalence G).refl D
    -- Verify second part
    intro v h_neg
    rw [h]
    simp
  · -- Case: S ≠ G.V
    let h_conn' := h_conn -- Unsimplified copy for later
    dsimp [graph_connected] at h_conn
    specialize h_conn S
    have : ∃ (v w : G.V), v ∈ S ∧ w ∉ S := by
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
    have : ∃ E : CFDiv G, linear_equiv G E1 E ∧ (∀ v : G.V, E v < 0 → v ∈ S) := by
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
            push Not at h
            dsimp [max]
            split_ifs at * with hle
            · linarith
            · simp only [zero_mul, add_zero] at *; linarith
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
termination_by ((univ : Finset G.V).card - S.card)
decreasing_by
  have h_succ: (insert w S).card = S.card + 1 := by
    apply Finset.card_eq_succ.mpr
    use w, S
  rw [h_succ]
  refine Nat.sub_succ_lt_self univ.card S.card ?_
  have : (insert w S).card ≤ (univ : Finset G.V).card := by
    apply Finset.card_le_card
    simp
  linarith

/-- Every divisor can have its debt concentrated on on vertex, as long as the graph is connected. That is, D is linearly equivalent to a q-effective divisor. -/
theorem q_effective_exists {G : CFGraph} (h_conn : graph_connected G) (q : G.V) (D : CFDiv G) :
  ∃ (E : CFDiv G), q_effective q E ∧ linear_equiv G D E := by
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
## The q-reduction partial order

A firing script $\sigma$ is a *$q$-reducer* if $\sigma(q) \leq \sigma(v)$ for all $v$,
meaning $q$ is fired the least (or not at all relative to the others). The relation
`reduces_to G q D₁ D₂` holds when $D_2$ is obtained from $D_1$ by applying a $q$-reducer
script, i.e. $D_2 = D_1 + \mathrm{prin}(\sigma)$ for some $q$-reducer $\sigma$.

This relation is reflexive and transitive, and in connected graphs it is also antisymmetric
(`reduces_to_antisymmetric`), making it a partial order on $q$-effective divisors. The
antisymmetry relies on the fact that a firing script with trivial principal divisor must
be constant (`constant_script_of_zero_prin`).
-/

/-- A firing script `σ` is a *$q$-reducer* if `q` is fired the minimum number of times:
`σ q ≤ σ v` for all `v`. -/
def q_reducer (G : CFGraph) (q : G.V) (σ : firing_script G) : Prop :=
  ∀ v : G.V, σ q ≤ σ v

/-- `reduces_to G q D₁ D₂` holds when `D₂` is obtained from `D₁` by applying a $q$-reducer
script: `D₂ = D₁ + prin G σ` for some `σ` with `σ q ≤ σ v` for all `v`. -/
def reduces_to (G : CFGraph) (q : G.V) (D₁ D₂: CFDiv G) : Prop :=
  ∃ σ : firing_script G, q_reducer G q σ ∧ D₂ = D₁ + prin G σ

/-- The `reduces_to` relation is reflexive: any divisor reduces to itself via the zero script. -/
lemma reduces_to_reflexive (G : CFGraph) (q : G.V) (D : CFDiv G) :
  reduces_to G q D D := by
  use 0
  refine ⟨?_, ?_⟩
  · intro v
    repeat rw [Pi.zero_apply]
  · rw [(prin G).map_zero]
    simp

/-- The `reduces_to` relation is transitive: composing two $q$-reducer scripts yields a $q$-reducer script. -/
lemma reduces_to_transitive (G : CFGraph) (q : G.V) (D₁ D₂ D₃ : CFDiv G) :
  reduces_to G q D₁ D₂ → reduces_to G q D₂ D₃ → reduces_to G q D₁ D₃ := by
  rintro ⟨σ₁, h_reducer_1, h_D2_eq⟩ ⟨σ₂, h_reducer_2, h_D3_eq⟩
  use σ₁ + σ₂
  refine ⟨?_, ?_⟩
  ·
    intro v
    repeat rw [Pi.add_apply]
    apply add_le_add (h_reducer_1 v) (h_reducer_2 v)
  ·
    rw [(prin G).map_add, ← add_assoc]
    rw [← h_D2_eq, ← h_D3_eq]

/-- In a connected graph, a firing script with zero principal divisor must be constant.
This is the key step in proving antisymmetry of `reduces_to`. -/
lemma constant_script_of_zero_prin {G : CFGraph} (h_conn : graph_connected G) (σ : firing_script G) : prin G σ = 0 → ∀ (v w : G.V), σ v = σ w := by
  intro zero_eq
  let min_exists := Finset.exists_min_image Finset.univ σ (by use Classical.arbitrary G.V; simp)
  rcases min_exists with ⟨q, ⟨_,h_reducer⟩⟩
  have h_reducer : ∀ v : G.V, σ q ≤ σ v := by
    intro v; specialize h_reducer v
    simp at h_reducer; exact h_reducer
  let S := Finset.univ.filter (λ v => σ v = σ q)
  have q_in_S : q ∈ S := by
    dsimp [S]
    simp
  have S_full : ∀ v : G.V, v ∈ S := by
    by_contra! v_nin_S
    rcases v_nin_S with ⟨v, h_v⟩
    have h : ∃ (u v : G.V), u ∈ S ∧ v ∉ S := by
      use q, v
    have := h_conn S h
    rcases this with ⟨u, h_u_in_S, w, h_w_nin_S, h_edge⟩
    have nonneg_terms: ∀ w : G.V, (σ w - σ u) * (num_edges G u w : ℤ) ≥ 0 := by
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
    have pos_term : ∃ (w : G.V), (σ w - σ u) * (num_edges G u w : ℤ) > 0 := by
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
    have : ∑ u_1 : G.V, (σ u_1 - σ u) * ↑(num_edges G u u_1) >0 := by
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
  have eq_q : ∀ v : G.V, σ v = σ q := by
    intro v; specialize S_full v
    dsimp [S] at S_full; simp at S_full
    exact S_full
  rw [eq_q v, eq_q w]

/-- In a connected graph, the `reduces_to` relation is antisymmetric, completing the proof
that it is a partial order on $q$-effective divisors. -/
lemma reduces_to_antisymmetric {G : CFGraph} (h_conn : graph_connected G) (q : G.V) (D₁ D₂ : CFDiv G) :
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

  have : ∀ v : G.V, σ₁ v = σ₁ q := by
    intro v
    specialize h_reducer_1 v
    specialize h_reducer_2 v
    dsimp [σ] at prin_sum_zero
    specialize prin_sum_zero q v
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

A $q$-effective divisor $D$ is *$q$-reduced* if, for every nonempty set $S \subseteq G.V \setminus \{q\}$,
some vertex in $S$ would go into debt if $S$ were fired ([Corry-Perkinson], Definition 3.4).
Equivalently, $D$ is the maximum element of its linear equivalence class in the $q$-reduction
partial order.

The main results of this section are:
- Every divisor has a unique $q$-reduced representative (`exists_q_reduced_representative`,
  `q_reduced_unique`), corresponding to [Corry-Perkinson], Theorem 3.6.
- A divisor is winnable if and only if its $q$-reduced representative is effective
  (`winnable_iff_q_reduced_effective`), corresponding to [Corry-Perkinson], Corollary 3.7.

The existence proof proceeds by defining an `active` vertex (one that can still be fired
while maintaining $q$-effectivity) and showing that the `reduction_excess` — the total chips
at active vertices — strictly decreases at each reduction step.
-/

/-- A divisior is q-reduced if it is effective away from q, but firing any vertex set disjoint from q puts some vertex into debt.
[Corry-Perkinson], Definition 3.4 -/
def q_reduced (G : CFGraph) (q : G.V) (D : CFDiv G) : Prop :=
  q_effective q D ∧
  (∀ S : Finset G.V, S ⊆ (Finset.univ.filter (· ≠ q)) → S.Nonempty →
    ∃ v ∈ S, D v < ∑ w ∈  (univ.filter (λ x => x ∉ S)), (num_edges G v w : ℤ))



/-- Helper lemma: a firing script can be understood as first firing the set where the maximum occurs, and no debt is created at this step unless it will remain at the end. -/
lemma maxset_of_script (G : CFGraph) (σ : firing_script G) : ∃ S : Finset G.V, Nonempty S ∧ ∀ v ∈ S, (∀ w : G.V, σ w ≤ σ v ∧ (w ∈ S → σ w = σ v)) ∧ -(prin G σ v) ≥ ∑ w ∈ (univ.filter (λ x => x ∉ S)), (num_edges G v w : ℤ) := by
  let max_exists := Finset.exists_max_image Finset.univ σ (by use Classical.arbitrary G.V; simp)
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
lemma q_reducer_of_add_princ_reduced (G : CFGraph) (q : G.V) (D : CFDiv G) (σ : firing_script G) :
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
    unfold q_effective; push Not; use v
    suffices v ≠ q by simp [this, dv_neg]
    contrapose! q_nin_S
    rw [← q_nin_S]; exact v_in_S
  have ineq : (-σ) v ≤ (-σ) q := ((h_S q q_S).1 v).1
  repeat rw [Pi.neg_apply] at ineq
  linarith

/-- Alternative description of q-reduced divisors: maximum q-effective diviors with respect to reduction in a linear equivalence class.. -/
lemma maximum_of_q_reduced (G : CFGraph) {q : G.V} {D : CFDiv G} (q_eff : q_effective q D) : q_reduced G q D → ∀ D' : CFDiv G, linear_equiv G D D' → q_effective q D' → reduces_to G q D' D := by
  intro h_q_reduced D' h_lequiv h_eff
  unfold linear_equiv at h_lequiv
  simp [principal_iff_eq_prin] at h_lequiv
  rcases h_lequiv with ⟨σ, D'_eq⟩
  have D'_eq : D' = D + prin G σ := by
    rw [← D'_eq]; simp
  rcases (maxset_of_script G σ) with ⟨S, S_nonempty, h_S⟩
  have q_S : q ∈ S := by
    contrapose! h_q_reduced with q_nin_S
    unfold q_reduced; push Not
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
lemma q_reduced_of_maximal {G : CFGraph} (h_conn : graph_connected G) {q : G.V} {D : CFDiv G} (q_eff : q_effective q D) :  (∀ D' : CFDiv G, linear_equiv G D D' → q_effective q D' → reduces_to G q D' D) →  q_reduced G q D := by
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
    let σ : firing_script G := λ v => if v ∈ S then 1 else 0
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
lemma helper_q_reduced_of_effective_is_effective (G : CFGraph) (q : G.V) (E E' : CFDiv G) :
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

/-- A winnable $q$-reduced divisor is effective. -/
lemma effective_of_winnable_and_q_reduced (G : CFGraph) (q : G.V) (D : CFDiv G) :
  winnable G D → q_reduced G q D → effective D := by
  intro h_winnable h_qred
  rcases h_winnable with ⟨E, h_eff_E, h_equiv⟩
  have h_equiv' : linear_equiv G E D := by
    exact (linear_equiv_is_equivalence G).symm h_equiv
  exact helper_q_reduced_of_effective_is_effective G q E D h_eff_E h_equiv' h_qred

/-- The q-reduced representative of a divisor class is unique.
[Corry-Perkinson], Theorem 3.6, part 2 (uniqueness). -/
theorem q_reduced_unique (G : CFGraph) (q : G.V) (D₁ D₂ : CFDiv G) :
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
  have : ∀ v : G.V, σ v = σ q := by
    intro v
    specialize h_reducer_1 v
    specialize h_reducer_2 v
    repeat rw [Pi.neg_apply] at h_reducer_2
    linarith
  have : prin G σ = (0 : CFDiv G) := by
    funext v
    unfold prin
    dsimp
    simp [this]
  rw [this] at h_D2_eq
  apply sub_eq_zero.mp at h_D2_eq
  rw [h_D2_eq]



/-- A vertex is called ``active'' if there exists a firing script that leaves the divisor effective away from q, does not fire q, and fires at least once at that vertex. -/
def active (G : CFGraph) (q : G.V) (D : CFDiv G) (v : G.V) : Prop :=
  ∃ σ : firing_script G, q_reducer G q σ ∧ q_effective q (D + prin G σ) ∧ σ q < σ v

/-- A $q$-effective divisor with no active vertices is $q$-reduced. -/
lemma q_reduced_of_no_active (G :CFGraph) {q : G.V} {D : CFDiv G} (h_eff : q_effective q D) (h_no_active : ∀ v : G.V, ¬ active G q D v) :
  q_reduced G q D := by
  contrapose! h_no_active with h_not_q_reduced
  dsimp [q_reduced] at h_not_q_reduced
  push Not at h_not_q_reduced
  rcases h_not_q_reduced h_eff with ⟨S, h_S_subset, h_S_nonempty, h_outdeg⟩
  have q_nin_S : q ∉ S := by
    intro h_contra
    have := h_S_subset h_contra
    simp at this
  -- Construct a firing script that fires all vertices in S
  let σ : firing_script G := λ v => if v ∈ S then 1 else 0
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
    have simp_ite : ∀ x_1 : G.V, ((if x_1 ∈ S then 1 else 0) - 1) = -(if x_1 ∈ S then 0 else 1) := by
      intro x_1
      by_cases h_x1 : x_1 ∈ S
      simp [h_x1]
      simp [h_x1]
    suffices (∑ x_1 : G.V, if x_1 ∈ S then 0 else ↑(num_edges G x x_1)) ≤ D x by
      simp [simp_ite,this]
    specialize h_outdeg x h_x
    have : (∑ w ∈ Finset.filter (fun x ↦ x ∉ S) univ, ↑(num_edges G x w) : ℤ) = (∑ x_1 : G.V, if x_1 ∈ S then 0 else ↑(num_edges G x x_1)) := by
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

/-- The total chips held at active vertices of `D`. This quantity strictly decreases at each
step of the $q$-reduction algorithm, providing the termination measure for
`q_effective_to_q_reduced`. -/
noncomputable def reduction_excess (G : CFGraph) (q : G.V) (D : CFDiv G) : ℤ := by
  classical
  exact (∑ v : G.V, if active G q D v then D v else 0)


/-- The reduction excess is nonnegative for $q$-effective divisors, since active vertices
satisfy `v ≠ q` and thus `D v ≥ 0`. -/
lemma reduction_excess_nonneg (G : CFGraph) {q : G.V} {D : CFDiv G} (h_eff : q_effective q D) :
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

/-- In a connected graph, every $q$-effective divisor is linearly equivalent to a $q$-reduced
divisor. The proof is by induction on `reduction_excess`. -/
theorem q_effective_to_q_reduced {G : CFGraph} (h_conn : graph_connected G) {q : G.V} {D : CFDiv G} (h_eff : q_effective q D) :
  ∃ E : CFDiv G, q_reduced G q E ∧ linear_equiv G D E := by
  -- Use induction on reduction_excess
  classical -- In order to filter using the undecidable "active"
  let S := Finset.univ.filter (λ v : G.V => active G q D v)
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
    have : ∃ v : G.V, active G q D v := by
      contrapose! h_S_empty with h_no_active
      dsimp [S]
      simp [h_no_active]
    rcases this with ⟨v_active, h_v_active⟩
    have : ∃ (v q : G.V), v ∈ S ∧ q ∉ S := by
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

    have h_active_shrinks (x : G.V): active G q D' x → active G q D x := by
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

    have chips_to_inactive_per_edge (u x : G.V) : ¬ active G q D x → (σ u - σ x) * ↑(num_edges G x u) ≥ 0 := by
      intro h_inactive_D
      dsimp [D']
      simp
      apply mul_nonneg
      · -- Show σ u - σ x ≥ 0
        have : σ x ≤ σ q := by
          dsimp [active] at h_inactive_D
          push Not at h_inactive_D
          specialize h_inactive_D σ
          exact h_inactive_D h_reducer h_eff'
        have : σ u ≥ σ q := by
          specialize h_reducer u
          linarith
        linarith
      · -- Show num_edges G x u ≥ 0
        simp

    have chips_to_inactive (x : G.V) : ¬ active G q D x → D x ≤ D' x := by
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
      have h (D : CFDiv G) : ∑ x ∈ Finset.filter (active G q D) univ, D x = deg D - ∑ x ∈ Finset.filter (fun v => ¬ active G q D v) univ, D x := by
        dsimp [deg]
        rw [← Finset.sum_filter_add_sum_filter_not univ (fun v => active G q D v)]
        simp
      rw [h D', h D]
      have : deg D = deg D' :=
        linear_equiv_preserves_deg G D D' D_equiv_D'
      rw [← this]
      simp
      -- Write as a sum over all vertices in order to compare terms
      have h (D : CFDiv G) : ∑ x ∈ Finset.filter (fun v => ¬ active G q D v) univ, D x = ∑ x : G.V, if ¬ active G q D x then D x else 0 := by
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
          push Not at h_inactive_D
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

/-- Every divisor is linearly equivalent to some $q$-reduced divisor.
[Corry-Perkinson], Theorem 3.6, part 1 (existence). -/
theorem exists_q_reduced_representative {G : CFGraph} (h_conn : graph_connected G) (q : G.V) (D : CFDiv G) :
  ∃ D' : CFDiv G, linear_equiv G D D' ∧ q_reduced G q D' :=
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

/-- Every divisor is linearly equivalent to exactly one $q$-reduced divisor.
[Corry-Perkinson], Theorem 3.6 (existence and uniqueness combined). -/
lemma unique_q_reduced {G : CFGraph} (h_conn : graph_connected G) (q : G.V) (D : CFDiv G) :
  ∃! D' : CFDiv G, linear_equiv G D D' ∧ q_reduced G q D' := by
  -- Prove existence and uniqueness separately
  have h_exists : ∃ D' : CFDiv G, linear_equiv G D D' ∧ q_reduced G q D' := by
    exact exists_q_reduced_representative h_conn q D

  -- Combine existence and uniqueness using the standard constructor
  obtain ⟨D', hD'⟩ := h_exists
  refine ExistsUnique.intro D' hD' (fun y hy => ?_)
  have h_equiv : linear_equiv G y D' := by
    exact (linear_equiv_is_equivalence G).trans ((linear_equiv_is_equivalence G).symm (hy.1)) (hD'.1)
  exact q_reduced_unique G q y D' ⟨hy.2, hD'.2, h_equiv⟩

/-- A divisor is winnable if and only if its q-reduced representative is effective.
[Corry-Perkinson], Corollary 3.7, rephrased. -/
theorem winnable_iff_q_reduced_effective {G : CFGraph} (h_conn : graph_connected G) (q : G.V) (D : CFDiv G) :
  winnable G D ↔ ∃ D' : CFDiv G, linear_equiv G D D' ∧ q_reduced G q D' ∧ effective D' := by
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
