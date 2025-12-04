import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.BigOperators.Group.Finset
import ChipFiringWithLean.Basic
import ChipFiringWithLean.Config
import ChipFiringWithLean.Orientation
import Paperproof

set_option linter.unusedVariables false
set_option trace.split.failure true
set_option linter.unusedSectionVars false

open Multiset Finset

-- Assume V is a finite type with decidable equality
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]

-- Helper lemma: An effective divisor with degree 0 is the zero divisor.
lemma effective_deg_zero_is_zero_divisor (D : CFDiv V) (h_eff : effective D) (h_deg_zero : deg D = 0) :
  D = (λ _ => 0) := by
  apply funext
  intro v
  have h_all_nonneg : ∀ x, D x ≥ 0 := h_eff
  have h_sum_eq_zero : ∑ x in Finset.univ, D x = 0 := by
    unfold deg at h_deg_zero
    exact h_deg_zero
  exact Finset.sum_eq_zero_iff_of_nonneg (λ x _ => h_all_nonneg x) |>.mp h_sum_eq_zero v (Finset.mem_univ v)

-- Helper lemma: The zero divisor is winnable.
lemma winnable_zero_divisor (G : CFGraph V) : winnable G (λ _ => 0) := by
  let D₀ : CFDiv V := (λ _ => 0)
  unfold winnable
  simp only [Div_plus, Set.mem_setOf_eq] -- Use simp to unfold Div_plus and resolve membership
  use D₀ -- D' = D₀
  constructor
  · -- D₀ is effective
    unfold effective
    intro v
    simp [D₀]
  · -- linear_equiv G D₀ D₀
    unfold linear_equiv
    simp only [sub_self, D₀] -- D₀ refers to the local let D₀
    exact AddSubgroup.zero_mem (principal_divisors G)

/-- Definition of maximal winnable divisor -/
def maximal_winnable (G : CFGraph V) (D : CFDiv V) : Prop :=
  winnable G D ∧ ∀ v : V, ¬winnable G (λ w => D w + if w = v then 1 else 0)

/-- A divisor is maximal unwinnable if it is unwinnable but adding
    a chip to any vertex makes it winnable -/
def maximal_unwinnable (G : CFGraph V) (D : CFDiv V) : Prop :=
  ¬winnable G D ∧ ∀ v : V, winnable G (λ w => D w + if w = v then 1 else 0)

/-- Given an acyclic orientation O with a unique source q, returns a configuration c(O) -/
def orientation_to_config (G : CFGraph V) (O : CFOrientation G) (q : V)
    (h_acyclic : is_acyclic G O) (h_unique_source : ∀ w, is_source G O w → w = q) : Config V q :=
  config_of_source h_acyclic h_unique_source

/-- The genus of a graph is its cycle rank: |E| - |V| + 1 -/
def genus (G : CFGraph V) : ℤ :=
  Multiset.card G.edges - Fintype.card V + 1

/-- A divisor has rank -1 if it is not winnable -/
def rank_eq_neg_one_wrt_winnability (G : CFGraph V) (D : CFDiv V) : Prop :=
  ¬(winnable G D)

/-- A divisor has rank -1 if its complete linear system is empty -/
def rank_eq_neg_one_wrt_complete_linear_system (G : CFGraph V) (D : CFDiv V) : Prop :=
  complete_linear_system G D = ∅

/-- Given a divisor D and amount k, returns all possible ways
    to remove k dollars from D (i.e. all divisors E where D-E has degree k) -/
def remove_k_dollars (D : CFDiv V) (k : ℤ) : Set (CFDiv V) :=
  {E | effective E ∧ deg E = k}

lemma remove_k_dollars_nonempty (D : CFDiv V) (k : ℕ) : k ≥ 0 → (remove_k_dollars D k).Nonempty := by
  let v : V := Classical.arbitrary V
  let E₁ : CFDiv V := one_chip v
  have eff : effective E₁ := by
    unfold effective
    intro w
    dsimp [E₁, one_chip]
    split_ifs with h
    norm_num
    norm_num
  have deg_E: deg_hom E₁ = 1 := by
    dsimp [deg_hom, E₁, one_chip]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_eq_zero]
    -- Now evaluate that cardinality as 1
    -- rewrite that set as {v}
    have h_card : (Finset.univ.filter (λ x => x = v)).card = 1 := by
      rw [Finset.card_eq_one]
      use v
      -- Do a double-inclusion proof, I guess?
      ext x
      constructor
      · intro h
        rw [Finset.mem_singleton]
        exact (Finset.mem_filter.mp h).2
      · intro h
        rw [Finset.mem_filter]
        rw [Finset.mem_singleton] at h
        exact ⟨Finset.mem_univ x, h⟩
    rw [h_card]
    norm_num
    intro x h
    rfl
  let E := k • E₁
  have eff : effective E := eff_of_smul_eff k E₁ eff
  have deg_E : deg E = k := by
    dsimp [E]
    have := AddMonoidHom.map_nsmul deg_hom E₁ k
    rw [deg_E] at this
    dsimp [deg_hom] at this
    dsimp [deg_hom]
    rw [this]
    ring
  intro h_nonneg
  dsimp [remove_k_dollars]
  use E
  constructor
  · exact eff
  · exact deg_E

/-- A divisor D has rank ≥ k if the game is winnable after removing any k dollars -/
def rank_geq (G : CFGraph V) (D : CFDiv V) (k : ℤ) : Prop :=
  ∀ E ∈ remove_k_dollars D k, winnable G (D-E)

lemma rank_geq_negone (G : CFGraph V) (D : CFDiv V) : rank_geq G D (-1) := by
  intro E h_E
  exfalso
  rcases h_E with ⟨h_eff_E, h_deg_E⟩
  apply deg_of_eff_nonneg at h_eff_E
  rw [deg_eq_deg_hom] at h_deg_E
  linarith

lemma deg_winnable_nonneg (G : CFGraph V) (D : CFDiv V) (h_winnable : winnable G D) : deg_hom D ≥ 0 := by
  rcases h_winnable with ⟨D', h_D'_eff, h_lequiv⟩
  have same_deg: deg_hom D = deg_hom D' := linear_equiv_preserves_deg G D D' h_lequiv
  rw [same_deg]
  dsimp [Div_plus] at h_D'_eff
  dsimp [deg_hom]
  refine Finset.sum_nonneg ?_
  intro v h_v
  exact h_D'_eff v

lemma rank_le_degree (G : CFGraph V) (D : CFDiv V) : ∀ (r : ℤ), r ≥ 0 → rank_geq G D r → r ≤ deg_hom D := by
  intro r r_nonneg h_rank
  contrapose! h_rank
  unfold rank_geq; push_neg
  have ex_E := remove_k_dollars_nonempty D
  specialize ex_E r.toNat
  have : r.toNat =r := by simp; assumption
  rw [this] at ex_E
  have : r.toNat ≥ 0 := by simp
  let ex_E := ex_E this
  rcases ex_E with ⟨E, h_E_eff, h_E_deg⟩
  use E
  constructor
  -- First conjunct: show that E is effecitive of the correct degree
  exact ⟨h_E_eff, h_E_deg⟩
  -- Second conjunct: show that D-E is not winnable
  contrapose! h_rank
  have deg_nonneg := deg_winnable_nonneg G (D-E) h_rank
  simp at deg_nonneg
  rw [deg_eq_deg_hom] at h_E_deg
  rw [h_E_deg] at deg_nonneg
  exact deg_nonneg

def rank_eq (G : CFGraph V) (D : CFDiv V) (r : ℤ) : Prop :=
  rank_geq G D r ∧ ¬(rank_geq G D (r+1))

lemma rank_exists_unique (G : CFGraph V) (D : CFDiv V) :
  ∃! r : ℤ, rank_eq G D r := by
  sorry

/-- Helper to check if a divisor has exactly k chips removed at some vertex -/
def has_k_chips_removed (D : CFDiv V) (E : CFDiv V) (k : ℕ) : Prop :=
  ∃ v : V, E = (λ w => D w - if w = v then k else 0)

/-- Helper to check if all k-chip removals are winnable -/
def all_k_removals_winnable (G : CFGraph V) (D : CFDiv V) (k : ℕ) : Prop :=
  ∀ E : CFDiv V, has_k_chips_removed D E k → winnable G E

/-- Helper to check if there exists an unwinnable configuration after removing k+1 chips -/
def exists_unwinnable_removal (G : CFGraph V) (D : CFDiv V) (k : ℕ) : Prop :=
  ∃ E : CFDiv V, effective E ∧ deg E = k + 1 ∧ ¬(winnable G (D-E))

/-- Lemma: If a divisor is winnable, there exists an effective divisor linearly equivalent to it -/
lemma winnable_iff_exists_effective (G : CFGraph V) (D : CFDiv V) :
  winnable G D ↔ ∃ D' : CFDiv V, effective D' ∧ linear_equiv G D D' := by
  unfold winnable Div_plus
  simp only [Set.mem_setOf_eq]

/-- Axiom: Rank existence and uniqueness -/
lemma rank_exists_unique_old (G : CFGraph V) (D : CFDiv V) :
  ∃! r : ℤ, (r = -1 ∧ ¬(winnable G D)) ∨
    (r ≥ 0 ∧ rank_geq G D r.toNat ∧ exists_unwinnable_removal G D r.toNat ∧
     ∀ k' : ℕ, k' > r.toNat → ¬(rank_geq G D k')) := by
    dsimp [ExistsUnique]
    by_cases h_winnable : winnable G D
    · -- Case 1: D is winnable
      let R : Set ℤ := { r | rank_geq G D r }
      -- R is bounded above
      have R_bdd : BddAbove R := by
        use (deg_hom D)
        intro r h_r

        by_cases h_r_neg : r < 0
        -- Subcase: r < 0
        have : deg_hom D ≥ 0 := by
          -- This can surely be shortened with some reusable lemmas
          rcases h_winnable with ⟨D', h_D'_eff, h_lequiv⟩
          have same_deg: deg_hom D = deg_hom D' := linear_equiv_preserves_deg G D D' h_lequiv
          rw [same_deg]
          dsimp [Div_plus] at h_D'_eff
          dsimp [deg_hom]
          refine Finset.sum_nonneg ?_
          intro v h_v
          exact h_D'_eff v
        linarith
        -- Subcase: r ≥ 0
        have r_nonneg : r ≥ 0 := by
          linarith
        have r_eq_toNat : r = r.toNat := by
          simp
          rw [max_eq_left r_nonneg]


        dsimp [R] at h_r
        dsimp [rank_geq] at h_r
        have ex_E := (remove_k_dollars_nonempty D r.toNat)
        rw [← r_eq_toNat] at ex_E
        have : r.toNat ≥ 0 := by simp
        let ex_E := ex_E this
        rcases ex_E with ⟨E, h_E_eff, h_E_deg⟩
        specialize h_r E ⟨h_E_eff, h_E_deg⟩
        dsimp [winnable] at h_r
        rcases h_r with ⟨D', h_D'_eff, h_lequiv⟩
        have deg_D'_nonneg : deg_hom D' ≥ 0 := by
          dsimp [Div_plus] at h_D'_eff
          dsimp [deg_hom]
          refine Finset.sum_nonneg ?_
          intro v h_v
          exact h_D'_eff v
        have deg_D'_eq : deg_hom D' = deg_hom D - deg_hom E := by
          have h := AddMonoidHom.map_sub deg_hom D E
          have h' := linear_equiv_preserves_deg G (D-E) D' h_lequiv
          simp at h'
          rw [h']
        rw [deg_D'_eq] at deg_D'_nonneg
        simp at h_E_deg
        rw [h_E_deg] at deg_D'_nonneg
        have : max r 0 ≥ r := by
          apply le_max_left
        linarith
      have R_fin : R.Finite := by
        -- Use that R is bounded
        sorry
      have R_zero : 0 ∈ R := by
        dsimp [R]
        dsimp [rank_geq]
        intro E h_E
        have E_zero : E = 0 := by
          sorry
        rw [E_zero]; simp
        sorry
      sorry
    · -- Case 2: D is not winnable
      use -1
      constructor
      left
      exact ⟨rfl, h_winnable⟩
      intro y h_y
      rcases h_y with h_y | h_y
      exact h_y.left
      rcases h_y with ⟨h_geq, h_rank_geq, h_exists_unwinnable, h_forall⟩
      exfalso
      unfold rank_geq at h_rank_geq
      contrapose! h_rank_geq
      have ex_E := remove_k_dollars_nonempty D y.toNat
      have : y.toNat ≥ 0 := by simp
      let ex_E := ex_E this
      rcases ex_E with ⟨E, h_E_eff, h_E_deg⟩
      use E
      constructor
      exact ⟨h_E_eff,h_E_deg⟩
      contrapose! h_winnable
      dsimp [winnable] at h_winnable
      rcases h_winnable with ⟨D', h_D'_eff, h_lequiv⟩
      use D' + E
      constructor
      apply eff_of_eff_add_eff D' E h_D'_eff h_E_eff
      unfold linear_equiv at h_lequiv
      unfold linear_equiv
      rw [sub_sub_eq_add_sub] at h_lequiv
      exact h_lequiv

/-- The rank function for divisors -/
noncomputable def rank (G : CFGraph V) (D : CFDiv V) : ℤ :=
  Classical.choose (rank_exists_unique G D)

/-- Definition: Properties of rank function with respect to effective divisors -/
def rank_effective_char (G : CFGraph V) (D : CFDiv V) (r : ℤ) :=
  rank G D = r ↔
  (∀ E : CFDiv V, effective E → deg E = r + 1 → ¬(winnable G (λ v => D v - E v))) ∧
  (∀ E : CFDiv V, effective E → deg E = r → winnable G (λ v => D v - E v))

/-- Definition (Axiomatic): Helper for rank characterization to get effective divisor -/
axiom rank_get_effective (G : CFGraph V) (D : CFDiv V) :
  ∃ E : CFDiv V, effective E ∧ deg E = rank G D + 1 ∧ ¬(winnable G (λ v => D v - E v))

/-- Rank satisfies the defining properties -/
axiom rank_spec (G : CFGraph V) (D : CFDiv V) :
  let r := rank G D
  (r = -1 ↔ ¬(winnable G D)) ∧
  (∀ k : ℕ, r ≥ k ↔ rank_geq G D k) ∧
  (∀ k : ℤ, k ≥ 0 → r = k ↔
    rank_geq G D k.toNat ∧
    exists_unwinnable_removal G D k.toNat ∧
    ∀ k' : ℕ, k' > k.toNat → ¬(rank_geq G D k'))

/-- Helpful corollary: rank = -1 exactly when divisor is not winnable -/
theorem rank_neg_one_iff_unwinnable (G : CFGraph V) (D : CFDiv V) :
  rank G D = -1 ↔ ¬(winnable G D) := by
  exact (rank_spec G D).1

/-- Lemma: If rank is not non-negative, then it equals -1 -/
lemma rank_neg_one_of_not_nonneg (G : CFGraph V) (D : CFDiv V) (h_not_nonneg : ¬(rank G D ≥ 0)) : rank G D = -1 := by
  -- rank_exists_unique gives ∃! r, P r ∨ Q r
  -- Classical.choose_spec gives (P r ∨ Q r) ∧ ∀ y, (P y ∨ Q y) → y = r, where r = rank G D
  have h_exists_unique_spec := Classical.choose_spec (rank_exists_unique G D)
  -- We only need the existence part: P r ∨ Q r
  have h_disjunction := h_exists_unique_spec.1
  -- Now use Or.elim on the disjunction
  apply Or.elim h_disjunction
  · -- Case 1: rank G D = -1 ∧ ¬(winnable G D)
    intro h_case1
    -- The goal is rank G D = -1, which is the first part of h_case1
    exact h_case1.1
  · -- Case 2: rank G D ≥ 0 ∧ rank_geq G D (rank G D).toNat ∧ ...
    intro h_case2
    -- This case contradicts the hypothesis h_not_nonneg
    have h_nonneg : rank G D ≥ 0 := h_case2.1
    -- Derive contradiction using h_not_nonneg
    exact False.elim (h_not_nonneg h_nonneg)
