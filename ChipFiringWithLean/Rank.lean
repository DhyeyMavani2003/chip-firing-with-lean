import ChipFiringWithLean.Basic
import Paperproof

set_option linter.unusedVariables false
set_option trace.split.failure true
set_option linter.unusedSectionVars false

open Multiset Finset

-- Assume V is a finite type with decidable equality
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]

-- This can be removed. It is now subsumed by eff_degree_zero in Basic.lean.
-- Helper lemma: An effective divisor with degree 0 is the zero divisor.
-- lemma effective_deg_zero_is_zero_divisor (D : CFDiv V) (h_eff : effective D) (h_deg_zero : deg D = 0) :
--   D = (λ _ => 0) := by
--   apply funext
--   intro v
--   have h_all_nonneg : ∀ x, D x ≥ 0 := h_eff
--   have h_sum_eq_zero : ∑ x in Finset.univ, D x = 0 := by
--     unfold deg at h_deg_zero
--     exact h_deg_zero
--   exact Finset.sum_eq_zero_iff_of_nonneg (λ x _ => h_all_nonneg x) |>.mp h_sum_eq_zero v (Finset.mem_univ v)

-- This can be removed. It is not used elsewhere.
-- Helper lemma: The zero divisor is winnable.
-- lemma winnable_zero_divisor (G : CFGraph V) : winnable G (λ _ => 0) := by
--   let D₀ : CFDiv V := (λ _ => 0)
--   unfold winnable
--   simp only [Div_plus, Set.mem_setOf_eq] -- Use simp to unfold Div_plus and resolve membership
--   use D₀ -- D' = D₀
--   constructor
--   · -- D₀ is effective
--     unfold effective
--     intro v
--     simp [D₀]
--   · -- linear_equiv G D₀ D₀
--     unfold linear_equiv
--     simp only [sub_self, D₀] -- D₀ refers to the local let D₀
--     exact AddSubgroup.zero_mem (principal_divisors G)

lemma winnable_equiv_winnable (G : CFGraph V) (D1 D2 : CFDiv V) :
  winnable G D1 → linear_equiv G D1 D2 → winnable G D2 := by
  intro h_winnable1 h_lequiv
  rcases h_winnable1 with ⟨D1', h_D1'_eff, h_lequiv1⟩
  use D1'
  constructor
  · -- Show that D1' is effective
    exact h_D1'_eff
  · -- Show that D2 is linearly equivalent to D1'
    have : linear_equiv G D2 D1 := by
      exact (linear_equiv_is_equivalence G).symm h_lequiv
    exact (linear_equiv_is_equivalence G).transitive this h_lequiv1

/-- Definition of maximal winnable divisor -/
def maximal_winnable (G : CFGraph V) (D : CFDiv V) : Prop :=
  winnable G D ∧ ∀ v : V, ¬winnable G (λ w => D w + if w = v then 1 else 0)

/-- A divisor is maximal unwinnable if it is unwinnable but adding
    a chip to any vertex makes it winnable -/
def maximal_unwinnable (G : CFGraph V) (D : CFDiv V) : Prop :=
  ¬winnable G D ∧ ∀ v : V, winnable G (D + one_chip v)

lemma maximal_unwinnable_preserved (G : CFGraph V) (D1 D2 : CFDiv V) :
  maximal_unwinnable G D1 → linear_equiv G D1 D2 → maximal_unwinnable G D2 := by
  intro h_max_unwin h_lequiv
  rcases h_max_unwin with ⟨h_unwin_D1, h_winnable_add⟩
  constructor
  · -- Show ¬winnable G D2
    contrapose! h_unwin_D1
    apply winnable_equiv_winnable G D2 D1 h_unwin_D1
    exact (linear_equiv_is_equivalence G).symm h_lequiv
  · -- Show ∀ v, winnable G (D2 + one_chip v)
    intro v
    specialize h_winnable_add v
    apply winnable_equiv_winnable G (D1 + one_chip v) (D2 + one_chip v) h_winnable_add
    -- Show linear equivalence
    unfold linear_equiv at *
    simp
    exact h_lequiv



-- /-- A divisor has rank -1 if it is not winnable -/
-- def rank_eq_neg_one_wrt_winnability (G : CFGraph V) (D : CFDiv V) : Prop :=
--   ¬(winnable G D)

-- /-- A divisor has rank -1 if its complete linear system is empty -/
-- def rank_eq_neg_one_wrt_complete_linear_system (G : CFGraph V) (D : CFDiv V) : Prop :=
--   complete_linear_system G D = ∅

/-- Given a divisor D and amount k, returns all possible ways
    to remove k dollars from D (i.e. all divisors E where D-E has degree k) -/
    -- [TODO]: refactor to give this a more descriptive name, e.g. set_eff_k
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
  have deg_E: deg E₁ = 1 := by
    dsimp [deg, E₁, one_chip]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_eq_zero]
    -- Now evaluate that cardinality as 1
    -- rewrite that set as {v}
    have h_card : (Finset.univ.filter (λ x => x = v)).card = 1 := by
      rw [Finset.card_eq_one]
      use v
      -- Do a double-inclusion proof, I guess? I'm sure there's a better way.
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
    have := AddMonoidHom.map_nsmul deg E₁ k
    rw [deg_E] at this
    dsimp [deg] at this
    dsimp [deg]
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

def rank_eq (G : CFGraph V) (D : CFDiv V) (r : ℤ) : Prop :=
  rank_geq G D r ∧ ¬(rank_geq G D (r+1))

lemma rank_geq_neg (G : CFGraph V) (D : CFDiv V) (k : ℤ): (k < 0) → rank_geq G D k := by
  intro k_neg E h_E
  exfalso
  rcases h_E with ⟨h_eff_E, h_deg_E⟩
  apply deg_of_eff_nonneg at h_eff_E
  linarith

lemma deg_winnable_nonneg (G : CFGraph V) (D : CFDiv V) (h_winnable : winnable G D) : deg D ≥ 0 := by
  rcases h_winnable with ⟨D', h_D'_eff, h_lequiv⟩
  have same_deg: deg D = deg D' := linear_equiv_preserves_deg G D D' h_lequiv
  rw [same_deg]
  dsimp [Div_plus] at h_D'_eff
  dsimp [deg]
  refine Finset.sum_nonneg ?_
  intro v h_v
  exact h_D'_eff v

lemma winnable_of_effective (G : CFGraph V) (D : CFDiv V) (h_eff : effective D) : winnable G D := by
  unfold winnable
  use D
  constructor
  · exact h_eff
  · unfold linear_equiv
    rw [sub_self]
    exact AddSubgroup.zero_mem (principal_divisors G)

lemma winnable_add_winnable (G : CFGraph V) (D1 D2 : CFDiv V)
    (h_winnable1 : winnable G D1) (h_winnable2 : winnable G D2) : winnable G (D1 + D2) := by
  rcases h_winnable1 with ⟨D1', h_D1'_eff, h_lequiv1⟩
  rcases h_winnable2 with ⟨D2', h_D2'_eff, h_lequiv2⟩
  use D1' + D2'
  constructor
  · -- Show that D1' + D2' is effective
    exact eff_of_eff_add_eff D1' D2' h_D1'_eff h_D2'_eff
  · -- Show that D1 + D2 is linearly equivalent to D1' + D2'
    unfold linear_equiv at *
    have : D1' + D2' - (D1 + D2) = (D1' - D1) + (D2' - D2) := by
      rw [sub_add_sub_comm]
    rw [this]
    exact AddSubgroup.add_mem (principal_divisors G) h_lequiv1 h_lequiv2

lemma rank_le_degree (G : CFGraph V) (D : CFDiv V) : ∀ (r : ℤ), r ≥ 0 → rank_geq G D r → r ≤ deg D := by
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
  rw [h_E_deg] at deg_nonneg
  exact deg_nonneg

lemma rank_geq_trans (G : CFGraph V) (D : CFDiv V) (r1 r2 : ℤ) :
  rank_geq G D r1 → r2 ≤ r1 → rank_geq G D r2 := by
  intro h_r1 h_leq
  unfold rank_geq at *
  contrapose! h_r1
  rcases h_r1 with ⟨E, ⟨h_E_eff,h_E_nonwin⟩⟩
  have ex_Ediff := remove_k_dollars_nonempty D (r1 - r2).toNat
  have diffNonneg: (r1 - r2).toNat = r1 - r2 := by
    simp
    exact h_leq
  rw [diffNonneg] at ex_Ediff
  have : (r1-r2).toNat ≥ 0 := by
    simp
  let ex_Ediff := ex_Ediff this
  rcases ex_Ediff with ⟨E_diff, ⟨h_Ediff_eff, h_Ediff_deg⟩⟩
  use E + E_diff
  constructor
  · -- Show that E + E_diff is effective of degree r2
    constructor
    apply eff_of_eff_add_eff E E_diff
    exact h_E_eff.left
    exact h_Ediff_eff
    -- Show degree
    have E_deg := h_E_eff.right
    simp at E_deg h_Ediff_deg ⊢
    linarith
  . -- Show that D - (E + E_diff) is not winnable
    contrapose! h_E_nonwin
    have E_diff_winnable := winnable_of_effective G E_diff h_Ediff_eff
    have sum_winnable := winnable_add_winnable G _ _ h_E_nonwin E_diff_winnable
    simp at sum_winnable
    exact sum_winnable

def lt_of_rank_geq_not (G : CFGraph V) (D : CFDiv V) (r1 r2 : ℤ) :
  rank_geq G D r1 → ¬(rank_geq G D r2) → r1 < r2 := by
  intro h_r1 h_r2
  contrapose! h_r2
  exact rank_geq_trans G D r1 r2 h_r1 h_r2

lemma rank_eq_neg_one_iff_unwinnable  (G : CFGraph V) (D : CFDiv V) :
  rank_eq G D (-1) ↔ ¬(winnable G D) := by
  constructor
  · -- Forward direction
    intro h
    rcases h with ⟨_, h_rank⟩
    contrapose! h_rank
    simp
    intro E h_E
    rcases h_E with ⟨h_eff_E, h_deg_E⟩
    have E_zero := eff_degree_zero _ h_eff_E h_deg_E
    simp [E_zero]
    exact h_rank
  · -- Backward direction
    intro h_unwinnable
    constructor
    · -- Show rank_geq G D (-1)
      apply rank_geq_neg G D (-1)
      norm_num
    · -- Show ¬(rank_geq G D 0)
      intro h_rank_geq
      specialize h_rank_geq 0
      contrapose! h_unwinnable
      rw [sub_zero] at h_rank_geq
      apply h_rank_geq
      constructor
      dsimp [effective]
      norm_num
      simp

lemma rank_nonneg_iff_winnable (G : CFGraph V) (D : CFDiv V) :
  rank_geq G D 0 ↔ winnable G D := by
  constructor
  · -- Forward direction
    intro h_rank
    specialize h_rank 0
    dsimp [remove_k_dollars] at h_rank
    simp at h_rank
    apply h_rank
    dsimp [effective]
    norm_num
  · -- Backward direction
    intro h_winnable
    intro E h_E
    rcases h_E with ⟨h_eff_E, h_deg_E⟩
    have E_zero := eff_degree_zero _ h_eff_E h_deg_E
    simp [E_zero]
    exact h_winnable

lemma rank_exists_helper (G : CFGraph V) (D : CFDiv V) (m : ℕ):  ¬ (rank_geq G D m) → ∃ r < (m:ℤ), rank_eq G D r := by
  -- Induction on m
  induction' m with m ih
  · -- Base case: m = 0
    intro h_rank_geq
    use (-1)
    constructor
    norm_num
    have h_r_geq := rank_geq_neg G D (-1) (by norm_num)
    exact ⟨h_r_geq, h_rank_geq⟩
  · -- Inductive step: m → m + 1
    intro h_rank_geq
    by_cases h_rank_m : rank_geq G D m
    · -- Case 1: rank_geq G D m holds
      use m
      exact ⟨by norm_num, ⟨h_rank_m, h_rank_geq⟩⟩
    · -- Case 2: rank_geq G D m does not hold
      specialize ih h_rank_m
      rcases ih with ⟨r, h_r_lt⟩
      use r
      have r_le : r < m+1 := by
        linarith [h_r_lt.left]
      exact ⟨r_le, h_r_lt.right⟩

lemma rank_exists (G : CFGraph V) (D : CFDiv V) :
  ∃ r : ℤ, rank_eq G D r := by
  let m := (deg D).toNat + 1
  have h_not_geq : ¬(rank_geq G D m) := by
    intro h_rank_geq
    have h_le := rank_le_degree G D m (by linarith) h_rank_geq
    have m_ge : m ≥ deg D + 1:= by
      dsimp [m]
      simp
    linarith
  have helper := rank_exists_helper G D m h_not_geq
  rcases helper with ⟨r, h_r_lt, h_rank_eq⟩
  exact ⟨r, h_rank_eq⟩

lemma rank_unique (G : CFGraph V) (D : CFDiv V) :
  ∀ r1 r2 : ℤ, rank_eq G D r1 → rank_eq G D r2 → r1 = r2 := by
  intro r1 r2 h_rank1 h_rank2
  rcases h_rank1 with ⟨h_r1_geq, h_r1_not_geq⟩
  rcases h_rank2 with ⟨h_r2_geq, h_r2_not_geq⟩
  have ineq1 : r1 < r2 + 1 := lt_of_rank_geq_not G D r1 (r2+1) h_r1_geq h_r2_not_geq
  have ineq2 : r2 < r1 + 1 := lt_of_rank_geq_not G D r2 (r1+1) h_r2_geq h_r1_not_geq
  linarith

/-- The rank function for divisors -/
noncomputable def rank (G : CFGraph V) (D : CFDiv V) : ℤ :=
  Classical.choose (rank_exists G D)

/-- Verify that rank_geq an rank_eq work correctly with the now-defined rank -/
lemma rank_geq_iff (G : CFGraph V) (D : CFDiv V) (k : ℤ) :
  rank_geq G D k ↔ rank G D ≥ k := by
  let r := rank G D
  have h_rank_eq := Classical.choose_spec (rank_exists G D)
  have h_r : rank_eq G D r := h_rank_eq
  constructor
  · -- Forward direction
    intro h_rank_geq
    have h_r_geq := h_r.right
    have := lt_of_rank_geq_not G D k (r+1) h_rank_geq h_r_geq
    linarith
  · -- Backward direction
    intro h_rank_leq
    have h_r_geq := h_r.left
    exact rank_geq_trans G D r k h_r_geq h_rank_leq

lemma rank_eq_iff (G : CFGraph V) (D : CFDiv V) (r : ℤ) :
  rank_eq G D r ↔ rank G D = r := by
  dsimp [rank_eq]
  have split_eq x: x = r ↔ (x ≥ r ∧ ¬(x ≥ r + 1)) := by
    rw [not_le]
    rw [Int.lt_add_one_iff]
    have helper := @le_antisymm_iff _ _ x r
    rw [helper, and_comm]
  rw [split_eq (rank G D)]
  rw [rank_geq_iff G D r, rank_geq_iff G D (r+1)]

-- These two definitions can be removed; they are not used elsewhere.
-- /-- Helper to check if a divisor has exactly k chips removed at some vertex -/
-- def has_k_chips_removed (D : CFDiv V) (E : CFDiv V) (k : ℕ) : Prop :=
--   ∃ v : V, E = (λ w => D w - if w = v then k else 0)

-- /-- Helper to check if all k-chip removals are winnable -/
-- def all_k_removals_winnable (G : CFGraph V) (D : CFDiv V) (k : ℕ) : Prop :=
--   ∀ E : CFDiv V, has_k_chips_removed D E k → winnable G E

/-- Helper to check if there exists an unwinnable configuration after removing k+1 chips -/
def exists_unwinnable_removal (G : CFGraph V) (D : CFDiv V) (k : ℕ) : Prop :=
  ∃ E : CFDiv V, effective E ∧ deg E = k + 1 ∧ ¬(winnable G (D-E))

/-- Lemma: If a divisor is winnable, there exists an effective divisor linearly equivalent to it -/
lemma winnable_iff_exists_effective (G : CFGraph V) (D : CFDiv V) :
  winnable G D ↔ ∃ D' : CFDiv V, effective D' ∧ linear_equiv G D D' := by
  unfold winnable Div_plus
  simp only [Set.mem_setOf_eq]

-- Can be removed; not used elsewhere.
-- /-- Definition: Properties of rank function with respect to effective divisors -/
-- def rank_effective_char (G : CFGraph V) (D : CFDiv V) (r : ℤ) :=
--   rank G D = r ↔
--   (∀ E : CFDiv V, effective E → deg E = r + 1 → ¬(winnable G (λ v => D v - E v))) ∧
--   (∀ E : CFDiv V, effective E → deg E = r → winnable G (λ v => D v - E v))

/-- Lemma: Helper for rank characterization to get effective divisor -/
lemma rank_get_effective (G : CFGraph V) (D : CFDiv V) :
  ∃ E : CFDiv V, effective E ∧ deg E = rank G D + 1 ∧ ¬(winnable G (D-E)) := by
  have h : rank_eq G D (rank G D) := by rw [rank_eq_iff]
  rcases h with ⟨_, h_r_not_geq⟩
  dsimp [rank_geq] at h_r_not_geq
  push_neg at h_r_not_geq
  rcases h_r_not_geq with ⟨E, ⟨h_E_eff, h_E_deg⟩, h_E_not_winnable⟩
  exact ⟨E, h_E_eff, h_E_deg, h_E_not_winnable⟩

-- Rank satisfies the defining properties -/
-- This statement is now subsumed by other lemmas, so it can be removed, and we will not try to resolve all "sorry"s.
-- lemma rank_spec (G : CFGraph V) (D : CFDiv V) :
--   let r := rank G D
--   (r = -1 ↔ ¬(winnable G D)) ∧
--   (∀ k : ℕ, r ≥ k ↔ rank_geq G D k) ∧
--   (∀ k : ℤ, k ≥ 0 → r = k ↔
--     rank_geq G D k.toNat ∧
--     exists_unwinnable_removal G D k.toNat ∧
--     ∀ k' : ℕ, k' > k.toNat → ¬(rank_geq G D k')) := by
--   let r := rank G D
--   have h_rank_eq := Classical.choose_spec (rank_exists G D)
--   have h_r : rank_eq G D r := h_rank_eq
--   rcases h_r with ⟨r_geq, r_le⟩
--   constructor
--   · -- First part: r = -1 ↔ ¬(winnable G D)
--     have h := rank_eq_neg_one_iff_unwinnable G D
--     simp [← h]
--     sorry
--   · -- Second part: ∀ k : ℕ, r ≥ k ↔ rank_geq G D k
--     constructor
--     sorry
--     · -- Third part: ∀ k : ℤ, k ≥ 0 → r = k ↔ ...
--       sorry



/-- Helpful corollary: rank = -1 exactly when divisor is not winnable -/
lemma rank_neg_one_iff_unwinnable (G : CFGraph V) (D : CFDiv V) :
  rank G D = -1 ↔ ¬(winnable G D) := by
  have h := rank_eq_neg_one_iff_unwinnable  G D
  simp [← h]
  have h_spec := Classical.choose_spec (rank_exists G D)
  let r := rank G D
  have h_r : rank_eq G D r := h_spec
  constructor
  -- Primal direction
  intro h
  have h₁ : r = -1 := h
  rw [h₁] at h_r
  exact h_r
  -- Converse direction
  intro h
  apply rank_unique G D r (-1) at h
  exact h
  exact h_r

/-- Lemma: If rank is not non-negative, then it equals -1 -/
lemma rank_neg_one_of_not_nonneg (G : CFGraph V) (D : CFDiv V) (h_not_nonneg : ¬(rank G D ≥ 0)) : rank G D = -1 := by
  have h_spec := Classical.choose_spec (rank_exists G D)
  let r := rank G D
  have h_r : rank_eq G D r := h_spec
  rcases h_r with ⟨h_r_geq, h_r_not_geq⟩
  have nwin : ¬(winnable G D) := by
    contrapose! h_not_nonneg
    apply (rank_nonneg_iff_winnable G D).mpr at h_not_nonneg
    have := lt_of_rank_geq_not G D 0 (r+1) h_not_nonneg h_r_not_geq
    linarith
  exact (rank_neg_one_iff_unwinnable G D).mpr nwin

/-- Lemma: rank ≥ -1 -/
lemma rank_geq_neg_one (G : CFGraph V) (D : CFDiv V) : rank G D ≥ -1 := by
  by_contra h
  have h_not_nonneg : ¬(rank G D ≥ 0) := by
    intro h_contra
    linarith
  have h_rank_neg_one := rank_neg_one_of_not_nonneg G D h_not_nonneg
  linarith
