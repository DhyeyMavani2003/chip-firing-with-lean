import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.BigOperators.Group.Finset
import ChipFiringWithLean.Basic
import Paperproof

set_option linter.unusedVariables false
set_option trace.split.failure true
set_option linter.unusedSectionVars false

open Multiset Finset

-- Assume V is a finite, nonempty type with decidable equality
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]

/-- A nonnegative configuration on a graph G with respect to a distinguished vertex q.
    Represents an element of ℤ(V\{q}) ⊆ ℤV with non-negativity constraints on V\{q}.

    Fields:
    * vertex_degree - Assignment of integers to vertices
    * non_negative_except_q - Proof that all values except at q are non-negative -/
structure Config (V : Type) (q : V) :=
  /-- Assignment of integers to vertices representing the number of chips at each vertex -/
  (vertex_degree : V → ℤ)
  /-- Proof that all vertices except q have non-negative values -/
  (non_negative_except_q : ∀ v : V, v ≠ q → vertex_degree v ≥ 0)

def toDiv {q : V} (c : Config V q) : CFDiv V :=
  λ v =>  if v = q then 0 else c.vertex_degree v

instance : CoeTC (Config V q) (CFDiv V) where
  coe := toDiv

lemma config_eff {q : V} (c : Config V q) : effective  (c : CFDiv V) := by
  intro v
  by_cases hv : v = q
  · -- Case v = q
    rw [hv]
    simp [toDiv]
  . -- Case v ≠ q
    simp [toDiv, hv]
    exact c.non_negative_except_q v hv

/-- The degree of a configuration is the sum of all values except at q.
    deg(c) = ∑_{v ∈ V\{q}} c(v) -/
def config_degree {q : V} (c : Config V q) : ℤ :=
  ∑ v in (univ.filter (λ v => v ≠ q)), c.vertex_degree v

lemma config_degree_eq_div_degree {q : V} (c : Config V q) : config_degree c = deg (c : CFDiv V)  := by
  dsimp [config_degree, deg, toDiv]
  -- Split the right sum into the sum over v ≠ q and the term at v = q
  have h_split (f : V → ℤ): ∑ v :V , f v = ∑ v in (univ.filter (λ v => v ≠ q)), f v + f q := by
    have h: q ∈ univ := by simp
    rw [Finset.sum_eq_sum_diff_singleton_add h f]
    apply (add_left_inj (f q)).mpr
    have same_domain: univ \ {q} = univ.filter (λ v => v ≠ q) := by
      ext v
      simp
    rw [same_domain]
  rw [h_split (λ v => if v = q then 0 else c.vertex_degree v)]
  simp
  apply Finset.sum_congr rfl
  intro v hv
  simp at hv
  simp [hv]

/-- Ordering on configurations: c ≥ c' if c(v) ≥ c'(v) for all v ∈ V.
    This is a pointwise comparison of the number of chips at each vertex. -/
def config_ge {q : V} (c c' : Config V q) : Prop :=
  ∀ v : V, v ≠ q → c.vertex_degree v ≥ c'.vertex_degree v

lemma config_ge_iff_div_ge {q : V} (c c' : Config V q) :
  config_ge c c' ↔ (c : CFDiv V)  ≥ (c' : CFDiv V) := by
  dsimp [config_ge, toDiv]
  constructor
  intro h_c v
  specialize h_c v
  by_cases hv : v = q
  · -- Case v = q
    rw [hv]
    dsimp [toDiv]
    simp
  . -- Case v ≠ q
    dsimp [toDiv]
    simp [hv]
    exact h_c hv
  -- Converse direction
  intro h_c v hv_ne_q
  specialize h_c v
  dsimp [toDiv] at h_c
  simp [hv_ne_q] at h_c
  exact h_c


-- Definition of the out-degree of a vertex v ∈ S with respect to a subset S ⊆ V \ {q}
-- This counts edges from v to vertices *outside* S.
-- outdeg_S(v) = |{ (v, w) ∈ E | w ∈ V \ S }|
def outdeg_S (G : CFGraph V) (q : V) (S : Finset V) (v : V) : ℤ :=
  -- Sum num_edges from v to w, where w is not in S and not q.
  ∑ w in (univ.filter (λ x => x ∉ S)), (num_edges G v w : ℤ)

-- Standard definition of Superstability:
-- A configuration c is superstable w.r.t. q if for every non-empty subset S of V \ {q},
-- there is at least one vertex v in S that cannot fire without borrowing,
-- meaning its chip count c(v) is strictly less than its out-degree w.r.t. S.
def superstable (G : CFGraph V) (q : V) (c : Config V q) : Prop :=
  ∀ S : Finset V, S ⊆ univ.filter (λ x => x ≠ q) → S.Nonempty →
    ∃ v ∈ S, c.vertex_degree v < outdeg_S G q S v

lemma superstable_iff_q_reduced (G : CFGraph V) (q : V) (c : Config V q) :
  superstable G q c ↔ q_reduced G q (c : CFDiv V) := by
  dsimp [superstable, q_reduced]
  constructor
  -- Forward direction
  intro h_superstable
  constructor
  -- Show c is nonnegative away from v
  intro v hv_ne_q
  dsimp [toDiv]
  simp [hv_ne_q]
  apply c.non_negative_except_q v hv_ne_q
  -- Show the outdegree condition
  intro S hS_subset hS_nonempty
  specialize h_superstable S hS_subset hS_nonempty
  rcases h_superstable with ⟨v, hv_in_S, hv_outdeg⟩
  use v
  constructor
  exact hv_in_S
  dsimp [outdeg_S] at hv_outdeg
  refine lt_of_le_of_lt  ?_ hv_outdeg
  dsimp [toDiv]
  by_cases hv_eq_q : v = q
  exfalso
  rw [hv_eq_q] at hv_in_S
  have h := hS_subset hv_in_S
  simp at h
  simp only [hv_eq_q]
  have cv_nonneg: c.vertex_degree v ≥ 0 := c.non_negative_except_q v hv_eq_q
  simp
  -- Reverse direction
  intro h_q_reduced
  rcases h_q_reduced with ⟨h_nonneg, h_outdeg⟩
  intro S hS_subset hS_nonempty
  specialize h_outdeg S hS_subset hS_nonempty
  rcases h_outdeg with ⟨v, hv_in_S, hv_outdeg⟩
  use v
  refine ⟨hv_in_S, ?_⟩
  dsimp [toDiv] at hv_outdeg
  have h_v_neq_q : v ≠ q := by
    intro hv_eq_q
    rw [hv_eq_q] at hv_in_S
    have h := hS_subset hv_in_S
    simp at h
  simp [h_v_neq_q] at hv_outdeg
  dsimp [outdeg_S]
  exact hv_outdeg

/-- A maximal superstable configuration has no legal firings and dominates all other superstable configs -/
def maximal_superstable {q : V} (G : CFGraph V) (c : Config V q) : Prop :=
  superstable G q c ∧ ∀ c' : Config V q, superstable G q c' → config_ge c' c

lemma smul_one_chip (k : ℤ) (v_chip : V) :
  (k • one_chip v_chip) = (fun v => if v = v_chip then k else 0) := by
  funext v
  rw [Pi.smul_apply]; unfold one_chip
  split_ifs with h
  · simp -- Goal is k • 1 = k
  · simp -- Goal is k • 0 = 0

-- Helper lemma: If D₁ ~ D₂, then D₁ + D ~ D₂ + D
lemma linear_equiv_add_congr_right_local (G : CFGraph V) (D_add : CFDiv V) {D1 D2 : CFDiv V} (h : linear_equiv G D1 D2) :
  linear_equiv G (D1 + D_add) (D2 + D_add) := by
  unfold linear_equiv at h ⊢
  have h_eq : (D2 + D_add) - (D1 + D_add) = D2 - D1 := by abel
  rw [h_eq]
  exact h

-- Helper lemma: Winnability is preserved under linear equivalence
lemma winnable_congr_local (G : CFGraph V) {D1 D2 : CFDiv V} (h_equiv : linear_equiv G D1 D2) :
  winnable G D1 ↔ winnable G D2 := by
  unfold winnable
  simp only [Div_plus, Set.mem_setOf_eq]
  apply Iff.intro
  { intro hw1
    rcases hw1 with ⟨E, hE_effective, hD1E_equiv⟩
    use E
    exact ⟨hE_effective, (linear_equiv_is_equivalence G).trans ((linear_equiv_is_equivalence G).symm h_equiv) hD1E_equiv⟩
  }
  { intro hw2
    rcases hw2 with ⟨E, hE_effective, hD2E_equiv⟩
    use E
    exact ⟨hE_effective, (linear_equiv_is_equivalence G).trans h_equiv hD2E_equiv⟩
  }
