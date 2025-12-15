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

abbrev Vtilde (q : V) : Finset V :=
  univ.filter (λ v => v ≠ q)

/-- A nonnegative configuration on a graph G with respect to a distinguished vertex q.
    Represents an element of ℤ(V\{q}) ⊆ ℤV with non-negativity constraints on V\{q}.

    Fields:
    * vertex_degree - Assignment of integers to vertices
    * non_negative_except_q - Proof that all values except at q are non-negative

    For convenience, vertex_degree is defined on all of V, and set to be 0 at q itself. -/
structure Config (V : Type) [DecidableEq V] [Fintype V] [Nonempty V] (q : V) :=
  /-- Assignment of integers to vertices representing the number of chips at each vertex -/
  (vertex_degree : CFDiv V)
  /-- Fix vertex_degree q = 0 for convenience -/
  (q_zero : vertex_degree q = 0)
  /-- Proof that all vertices except q have non-negative values -/
  (non_negative : ∀ v : V, vertex_degree v ≥ 0)

/-- The degree of a configuration is the sum of all values except at q.
    deg(c) = ∑_{v ∈ V\{q}} c(v) -/
def config_degree {q : V} (c : Config V q) : ℤ :=
  deg (c.vertex_degree)

/-- Convert a configuration to a divisor of specified
  degree d, but adding an appropraite number of chips
  at q. -/
def toDiv {q : V} (d : ℤ) (c : Config V q) : CFDiv V :=
  c.vertex_degree + (d - config_degree c) • (one_chip q)

lemma eq_config_iff_eq_vertex_degree {q : V} (c₁ c₂ : Config V q) :
  c₁ = c₂ ↔ c₁.vertex_degree = c₂.vertex_degree := by
  constructor
  -- Forward direction is clear
  intro h_eq
  rw [h_eq]
  -- Reverse direction takes more
  intro h_eq
  obtain ⟨vd₁, _, _⟩ := c₁
  obtain ⟨vd₂, _, _⟩ := c₂
  simp only [Config.mk.injEq]
  funext v
  apply congrFun h_eq v

lemma eq_config_iff_eq_div {q : V} (d : ℤ) (c₁ c₂ : Config V q) : c₁ = c₂ ↔ toDiv d c₁ = toDiv d c₂ := by
  constructor
  -- Forward direction is clear
  intro h_eq
  rw [h_eq]
  -- Reverse direction takes more
  intro h_eq
  apply congrFun at h_eq
  suffices h: c₁.vertex_degree = c₂.vertex_degree by
    obtain ⟨vd₁, _, _⟩ := c₁
    obtain ⟨vd₂, _, _⟩ := c₂
    simp only [Config.mk.injEq]
    funext v
    apply congrFun h v
  funext v
  specialize h_eq v
  dsimp [toDiv] at h_eq
  by_cases h_v : q = v
  . -- Case v = q
    rw [← h_v]
    rw [c₁.q_zero, c₂.q_zero]
  . -- Case v ≠ q
    simp [h_v] at h_eq
    exact h_eq

def to_qed {q : V} (d : ℤ) (c : Config V q) : q_eff_div V q :=
  {
    D := toDiv d c,
    h_eff := by
      intro v h_v
      dsimp [toDiv]
      simp [h_v]
      exact c.non_negative v
  }
def toConfig {q : V} (D : q_eff_div V q) : Config V q := {
  vertex_degree := D.D - (D.D q) • (one_chip q)
  q_zero := by
    rw [sub_apply,smul_apply]
    dsimp [one_chip]
    simp
  non_negative := by
    intro v
    by_cases h_v : v = q
    · -- Case v = q
      simp [h_v]
    . -- Case v ≠ q
      simp [h_v]
      exact D.h_eff v h_v
}

def config_degree_div_degree {q : V} (D : q_eff_div V q) : deg D.D = D.D q + config_degree (toConfig D) := by
  dsimp [config_degree, toConfig, one_chip]
  simp

lemma config_of_div_of_config (c : Config V q) (d : ℤ) (D : q_eff_div V q) :
  toConfig (to_qed d c) = c := by
  rcases c with ⟨vertex_degree, q_zero, non_negative⟩
  dsimp [to_qed, toConfig]
  simp
  apply funext
  intro v
  by_cases h_v : v = q
  . -- Case v = q
    simp [h_v]
    rw [q_zero]
  . -- Case v ≠ q
    dsimp [toDiv, one_chip]
    simp [h_v]

lemma qeff_divs_equal (D1 D2 : q_eff_div V q) :
  D1 = D2 ↔ D1.D = D2.D := by
  constructor
  intro h_eq
  rw [h_eq]
  -- Converse is the interesting direction
  intro h_eq
  rcases D1 with ⟨D1_D, D1_h_eff⟩
  rcases D2 with ⟨D2_D, D2_h_eff⟩
  simp [h_eq]
  simp at h_eq
  exact h_eq

lemma div_of_config_of_div (D : q_eff_div V q) :
  toDiv (deg D.D) (toConfig D) = D.D := by
  -- apply (qeff_divs_equal (to_qed (deg D.D) (toConfig D)) D).mpr
  -- dsimp [to_qe]
  funext v
  dsimp [toDiv]
  by_cases h: v ∈ Vtilde q
  . -- Case v ∈ Vtilde q
    simp [h]
    dsimp [toConfig]
    have : v ≠ q := by
      intro h_eq_q
      rw [h_eq_q] at h
      simp at h
    simp [this]
  . -- Case v ∉ Vtilde q
    simp [h]
    have : v = q := by
      contrapose! h
      simp [h]
    rw [this]
    unfold toConfig config_degree
    simp

@[simp] lemma eval_toDiv_q {q : V} (d : ℤ) (c : Config V q) :
  toDiv d c q = d - config_degree c := by
  dsimp [toDiv]
  simp [c.q_zero]

@[simp] lemma eval_toDiv_ne_q {q v : V} (d : ℤ) (c : Config V q) (h_v : v ≠ q) :
  toDiv d c v = c.vertex_degree v := by
  dsimp [toDiv]
  simp [h_v]


lemma config_eff {q : V} (d : ℤ) (c : Config V q) : effective (toDiv d c) ↔ d ≥ config_degree c := by
  constructor
  -- Effective implies d ≥ config_degree
  intro h_eff
  have h := h_eff q
  rw [eval_toDiv_q] at h
  linarith
  -- d ≥ config_degree implies effective
  intro h_deg
  intro v
  by_cases h_v : v = q
  · -- Case v = q
    simp [h_v, h_deg]
  · -- Case v ≠ q
    simp [h_v]
    exact c.non_negative v

-- lemma config_degree_eq_div_degree {q : V} (c : Config V q) : config_degree c = deg (c : CFDiv V)  := by
--   dsimp [config_degree, deg, toDiv]
--   -- Split the right sum into the sum over v ≠ q and the term at v = q
--   have h_split (f : V → ℤ): ∑ v :V , f v = ∑ v in (univ.filter (λ v => v ≠ q)), f v + f q := by
--     have h: q ∈ univ := by simp
--     rw [Finset.sum_eq_sum_diff_singleton_add h f]
--     apply (add_left_inj (f q)).mpr
--     have same_domain: univ \ {q} = univ.filter (λ v => v ≠ q) := by
--       ext v
--       simp
--     rw [same_domain]
--   rw [h_split (λ v => if v = q then 0 else c.vertex_degree v)]
--   simp
--   apply Finset.sum_congr rfl
--   intro v hv
--   simp at hv
--   simp [hv]

/-- Ordering on configurations: c ≥ c' if c(v) ≥ c'(v) for all v ∈ V.
    This is a pointwise comparison of the number of chips at each vertex.
    It also compares degree at v = q, but this is not a problem since that is always assumed zero.
    -/
def config_ge {q : V} (c c' : Config V q) : Prop :=
  ∀ v : V, c.vertex_degree v ≥ c'.vertex_degree v

instance : PartialOrder (Config V q) := {
  le := λ c₁ c₂ => c₁.vertex_degree ≤ c₂.vertex_degree,
  le_refl := by
    intro a
    simp
   ,
  le_trans := by
    intro c1 c2 c3 c1_le_c2 c2_le_c3
    dsimp at *
    exact le_trans c1_le_c2 c2_le_c3
  ,
  le_antisymm := by
    intro c1 c2 h_le h_ge
    dsimp at *
    have h_eq := le_antisymm h_le h_ge

    exact (eq_config_iff_eq_vertex_degree c1 c2).mpr h_eq
}


-- lemma config_ge_iff_div_ge {q : V} (d : ℤ) (c c' : Config V q) :
--   config_ge c c' ↔ (c : CFDiv V)  ≥ (c' : CFDiv V) := by
--   dsimp [config_ge, toDiv]
--   constructor
--   intro h_c v
--   specialize h_c v
--   by_cases hv : v = q
--   · -- Case v = q
--     rw [hv]
--     dsimp [toDiv]
--     simp
--   . -- Case v ≠ q
--     dsimp [toDiv]
--     simp [hv]
--     exact h_c hv
--   -- Converse direction
--   intro h_c v hv_ne_q
--   specialize h_c v
--   dsimp [toDiv] at h_c
--   simp [hv_ne_q] at h_c
--   exact h_c


-- Definition of the out-degree of a vertex v ∈ S with respect to a subset S ⊆ V \ {q}
-- This counts edges from v to vertices *outside* S.
-- outdeg_S(v) = |{ (v, w) ∈ E | w ∈ V \ S }|
-- The definition does not enforce v ∈ S, though it is only used in that case.
def outdeg_S (G : CFGraph V) (q : V) (S : Finset V) (v : V) : ℤ :=
  -- Sum num_edges from v to w, where w is not in S
  ∑ w in (univ \ S), (num_edges G v w : ℤ)

-- Standard definition of Superstability:
-- A configuration c is superstable w.r.t. q if for every non-empty subset S of V \ {q},
-- there is at least one vertex v in S that cannot fire without borrowing,
-- meaning its chip count c(v) is strictly less than its out-degree w.r.t. S.
def superstable (G : CFGraph V) (q : V) (c : Config V q) : Prop :=
  ∀ S ⊆  Vtilde q, S.Nonempty →
    ∃ v ∈ S, c.vertex_degree v < outdeg_S G q S v


lemma superstable_iff_q_reduced (G : CFGraph V) (q : V) (d : ℤ) (c : Config V q) :
  superstable G q c ↔ q_reduced G q (toDiv d c) := by

  -- Little rewriting needed later
  have comp_eq (S : Finset V): univ \ S = Finset.filter (λ w => w ∉ S) univ := by
    ext w
    simp

  dsimp [superstable, q_reduced]
  constructor
  -- Forward direction
  intro h_superstable
  constructor
  -- Show c is nonnegative away from v
  intro v hv_ne_q
  dsimp [toDiv]
  simp [hv_ne_q]
  exact c.non_negative v
  -- Show the outdegree condition
  intro S hS_subset hS_nonempty

  specialize h_superstable S hS_subset hS_nonempty
  rcases h_superstable with ⟨v, hv_in_S, hv_outdeg⟩
  use v
  constructor
  exact hv_in_S
  dsimp [outdeg_S] at hv_outdeg
  have h_v_ne_q : v ≠ q := by
    intro hv_eq_q
    rw [hv_eq_q] at hv_in_S
    have h := hS_subset hv_in_S
    simp at h
  rw [eval_toDiv_ne_q d c h_v_ne_q]
  rw [← comp_eq S]
  refine lt_of_le_of_lt  ?_ hv_outdeg
  apply le_refl
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
  rw [comp_eq S]
  exact hv_outdeg

/-- A maximal superstable configuration has no legal firings and is not ≤ any other superstable configuration. -/
def maximal_superstable {q : V} (G : CFGraph V) (c : Config V q) : Prop :=
  superstable G q c ∧ ∀ c' : Config V q, superstable G q c' → config_ge c' c → c' = c

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

/-- Definition: A burn list for a Configuraton c is a list [v_1, v_2, ..., v_n, q] of distinct vertices ending at q,
  where the following condition holds at each vertex *except q* (which plays a special role):
  if S is the set V \ {v_1, ..., v_(n-1)} (which contains v_n), then the out-degree of v_n with
  respect to S is greater than the number of chips at v_n. -/
def is_burn_list (G : CFGraph V) {q : V} (c : Config V q) (L : List V) : Prop :=
  match L with
  | [] => False
  | [x] => (x = q)
  | v :: w :: rest =>
      outdeg_S G q (univ \ (w :: rest).toFinset) v > c.vertex_degree v
      -- v isn't in the set made out of w :: rest
      ∧ ¬ (w :: rest).contains v
      ∧ is_burn_list G c (w :: rest)

structure burn_list (G : CFGraph V) {q : V} (c : Config V q) :=
  (list : List V)
  (h_burn_list : is_burn_list G c list)
