import ChipFiringWithLean.Basic
-- import Paperproof

set_option linter.unusedVariables false
set_option trace.split.failure true
set_option linter.unusedSectionVars false

open Multiset Finset

/-!
## The rank function

The *rank* of a divisor $D$ is the integer $r(D) \in \{-1, 0, 1, \ldots\}$ defined by
$r(D) \geq k$ iff $D - E$ is winnable for every effective divisor $E$ of degree $k$
([Corry-Perkinson], Section 5.1). Equivalently, $r(D) \geq 0$ iff $D$ is winnable,
and $r(D) = -1$ iff $D$ is unwinnable.

The rank is well-defined (`rank_exists`, `rank_unique`) and realized by the noncomputable
`rank` function. Key properties established here include:
- `rank_neg_one_iff_unwinnable`: $r(D) = -1 \iff D$ is unwinnable.
- `rank_nonneg_iff_winnable`: $r(D) \geq 0 \iff D$ is winnable.
- `rank_le_degree`: $r(D) \leq \deg(D)$ for $r(D) \geq 0$.
- `zero_divisor_rank`: $r(0) = 0$.

A divisor $D$ is *maximal unwinnable* if it is unwinnable but $D + \delta_v$ is winnable
for every vertex $v$. Such divisors arise in the proof of the Riemann-Roch theorem.
-/

/-- Winnability is preserved under linear equivalence. -/
lemma winnable_equiv_winnable (G : CFGraph) (D1 D2 : CFDiv G) :
  winnable G D1 → linear_equiv G D1 D2 → winnable G D2 := by
  rintro ⟨D1', h_D1'_eff, h_lequiv1⟩ h_lequiv
  exact ⟨D1', h_D1'_eff, (linear_equiv_is_equivalence G).trans ((linear_equiv_is_equivalence G).symm h_lequiv) h_lequiv1⟩


/-- A divisor is maximal unwinnable if it is unwinnable but adding
    a chip to any vertex makes it winnable -/
def maximal_unwinnable (G : CFGraph) (D : CFDiv G) : Prop :=
  ¬winnable G D ∧ ∀ v : G.V, winnable G (D + one_chip v)

/-- Being maximal unwinnable is preserved under linear equivalence. -/
lemma maximal_unwinnable_preserved (G : CFGraph) (D1 D2 : CFDiv G) :
  maximal_unwinnable G D1 → linear_equiv G D1 D2 → maximal_unwinnable G D2 := by
  rintro ⟨h_unwin_D1, h_winnable_add⟩ h_lequiv
  refine ⟨?_, ?_⟩
  · intro h_win_D2
    exact h_unwin_D1 <| winnable_equiv_winnable G D2 D1 h_win_D2 ((linear_equiv_is_equivalence G).symm h_lequiv)
  · intro v
    exact winnable_equiv_winnable G (D1 + one_chip v) (D2 + one_chip v) (h_winnable_add v) <| by
      unfold linear_equiv at *
      simpa using h_lequiv

/-- The set of effective divisors of degree `k`. Used to define `rank_geq`: `rank G D ≥ k`
means `D - E` is winnable for every `E` in `eff_of_degree D k`. -/
def eff_of_degree (D : CFDiv G) (k : ℤ) : Set (CFDiv G) :=
  {E | effective E ∧ deg E = k}

/-- For any natural number `k`, the set of effective divisors of degree `k` is nonempty. -/
lemma eff_of_degree_nonempty (D : CFDiv G) (k : ℕ) : k ≥ 0 → (eff_of_degree D k).Nonempty := by
  let v : G.V := Classical.arbitrary G.V
  intro h_nonneg
  dsimp [eff_of_degree]
  refine ⟨k • one_chip v, ?_, ?_⟩
  · exact (Eff G).nsmul_mem (eff_one_chip v) k
  · simpa [deg_one_chip] using (AddMonoidHom.map_nsmul deg (one_chip v) k)

/-- A divisor D has rank ≥ k if the game is winnable after removing any k dollars -/
def rank_geq (G : CFGraph) (D : CFDiv G) (k : ℤ) : Prop :=
  ∀ E ∈ eff_of_degree D k, winnable G (D-E)

/-- `rank_eq G D r` holds when `r` is exactly the rank of `D`: `rank_geq G D r` holds but
`rank_geq G D (r+1)` does not. -/
def rank_eq (G : CFGraph) (D : CFDiv G) (r : ℤ) : Prop :=
  rank_geq G D r ∧ ¬(rank_geq G D (r+1))

/-- `rank_geq G D k` holds vacuously for `k < 0`, since there are no effective divisors of
negative degree. -/
lemma rank_geq_neg (G : CFGraph) (D : CFDiv G) (k : ℤ): (k < 0) → rank_geq G D k := by
  intro k_neg E ⟨h_eff_E, h_deg_E⟩
  have := deg_of_eff_nonneg E h_eff_E
  linarith

/-- A winnable divisor has nonnegative degree. [Corry-Perkinson], Corollary 1.16 -/
lemma deg_winnable_nonneg (G : CFGraph) (D : CFDiv G) (h_winnable : winnable G D) : deg D ≥ 0 := by
  rcases h_winnable with ⟨D', h_D'_eff, h_lequiv⟩
  have same_deg: deg D = deg D' := linear_equiv_preserves_deg G D D' h_lequiv
  rw [same_deg]
  exact deg_of_eff_nonneg D' h_D'_eff

/-- Every effective divisor is winnable (it is already linearly equivalent to itself). -/
lemma winnable_of_effective (G : CFGraph) (D : CFDiv G) (h_eff : effective D) : winnable G D := by
  exact ⟨D, h_eff, by
    unfold linear_equiv
    rw [sub_self]
    exact AddSubgroup.zero_mem (principal_divisors G)⟩

/-- The sum of two winnable divisors is winnable. -/
lemma winnable_add_winnable (G : CFGraph) (D1 D2 : CFDiv G)
    (h_winnable1 : winnable G D1) (h_winnable2 : winnable G D2) : winnable G (D1 + D2) := by
  rcases h_winnable1 with ⟨D1', h_D1'_eff, h_lequiv1⟩
  rcases h_winnable2 with ⟨D2', h_D2'_eff, h_lequiv2⟩
  use D1' + D2'
  refine ⟨(Eff G).add_mem h_D1'_eff h_D2'_eff, ?_⟩
  ·
    unfold linear_equiv at *
    have : D1' + D2' - (D1 + D2) = (D1' - D1) + (D2' - D2) := by
      rw [sub_add_sub_comm]
    rw [this]
    exact AddSubgroup.add_mem (principal_divisors G) h_lequiv1 h_lequiv2

/-- If `rank_geq G D r` holds for some `r ≥ 0`, then `r ≤ deg D`. In particular,
`rank G D ≤ deg D` when `rank G D ≥ 0`. -/
lemma rank_le_degree (G : CFGraph) (D : CFDiv G) : ∀ (r : ℤ), r ≥ 0 → rank_geq G D r → r ≤ deg D := by
  intro r r_nonneg h_rank
  contrapose! h_rank
  unfold rank_geq; push Not
  have ex_E := eff_of_degree_nonempty D
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

/-- `rank_geq` is downward closed: if `rank G D ≥ r1` and `r2 ≤ r1`, then `rank G D ≥ r2`. -/
lemma rank_geq_trans (G : CFGraph) (D : CFDiv G) (r1 r2 : ℤ) :
  rank_geq G D r1 → r2 ≤ r1 → rank_geq G D r2 := by
  intro h_r1 h_leq
  unfold rank_geq at *
  contrapose! h_r1
  rcases h_r1 with ⟨E, ⟨h_E_eff,h_E_nonwin⟩⟩
  have ex_Ediff := eff_of_degree_nonempty D (r1 - r2).toNat
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
    apply (Eff G).add_mem
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

/-- If `rank_geq G D r1` holds but `rank_geq G D r2` does not, then `r1 < r2`. -/
def lt_of_rank_geq_not (G : CFGraph) (D : CFDiv G) (r1 r2 : ℤ) :
  rank_geq G D r1 → ¬(rank_geq G D r2) → r1 < r2 := by
  intro h_r1 h_r2
  contrapose! h_r2
  exact rank_geq_trans G D r1 r2 h_r1 h_r2

lemma rank_eq_neg_one_iff_unwinnable  (G : CFGraph) (D : CFDiv G) :
  rank_eq G D (-1) ↔ ¬(winnable G D) := by
  constructor
  · intro h
    rcases h with ⟨_, h_rank⟩
    contrapose! h_rank
    simp
    intro E h_E
    rcases h_E with ⟨h_eff_E, h_deg_E⟩
    have E_zero := eff_degree_zero _ h_eff_E h_deg_E
    simpa [E_zero] using h_rank
  · intro h_unwinnable
    refine ⟨rank_geq_neg G D (-1) (by norm_num), ?_⟩
    intro h_rank_geq
    specialize h_rank_geq 0
    apply h_unwinnable
    rw [sub_zero] at h_rank_geq
    apply h_rank_geq
    constructor
    · dsimp [effective]
      norm_num
    · simp

/-- `rank G D ≥ 0` if and only if `D` is winnable. -/
lemma rank_nonneg_iff_winnable (G : CFGraph) (D : CFDiv G) :
  rank_geq G D 0 ↔ winnable G D := by
  constructor
  · intro h_rank
    specialize h_rank 0
    rw [sub_zero] at h_rank
    exact h_rank <| by
      simp [eff_of_degree, effective]
  · intro h_winnable E ⟨h_eff_E, h_deg_E⟩
    have E_zero := eff_degree_zero _ h_eff_E h_deg_E
    simpa [E_zero] using h_winnable

/-- If `rank_geq G D m` fails for some natural number `m`, there exists an exact rank `r < m`. -/
lemma rank_exists_helper (G : CFGraph) (D : CFDiv G) (m : ℕ):  ¬ (rank_geq G D m) → ∃ r < (m:ℤ), rank_eq G D r := by
  induction m with
  | zero =>
  · intro h_rank_geq
    exact ⟨-1, by norm_num, rank_geq_neg G D (-1) (by norm_num), h_rank_geq⟩
  | succ m ih =>
    intro h_rank_geq
    by_cases h_rank_m : rank_geq G D m
    · exact ⟨m, by norm_num, h_rank_m, h_rank_geq⟩
    ·
      specialize ih h_rank_m
      rcases ih with ⟨r, h_r_lt, h_rank_eq⟩
      have r_le : r < m + 1 := by
        linarith [h_r_lt]
      exact ⟨r, r_le, h_rank_eq⟩

/-- Every divisor has a well-defined rank: there exists `r` with `rank_eq G D r`. -/
lemma rank_exists (G : CFGraph) (D : CFDiv G) :
  ∃ r : ℤ, rank_eq G D r := by
  let m := (deg D).toNat + 1
  have h_not_geq : ¬(rank_geq G D m) := by
    intro h_rank_geq
    have h_le := rank_le_degree G D m (by linarith) h_rank_geq
    have m_ge : m ≥ deg D + 1:= by
      dsimp [m]
      simp
    linarith
  rcases rank_exists_helper G D m h_not_geq with ⟨r, _, h_rank_eq⟩
  exact ⟨r, h_rank_eq⟩

/-- The rank of a divisor is unique: if `rank_eq G D r1` and `rank_eq G D r2`, then `r1 = r2`. -/
lemma rank_unique (G : CFGraph) (D : CFDiv G) :
  ∀ r1 r2 : ℤ, rank_eq G D r1 → rank_eq G D r2 → r1 = r2 := by
  rintro r1 r2 ⟨h_r1_geq, h_r1_not_geq⟩ ⟨h_r2_geq, h_r2_not_geq⟩
  have ineq1 : r1 < r2 + 1 := lt_of_rank_geq_not G D r1 (r2+1) h_r1_geq h_r2_not_geq
  have ineq2 : r2 < r1 + 1 := lt_of_rank_geq_not G D r2 (r1+1) h_r2_geq h_r1_not_geq
  linarith

/-- The rank function for divisors -/
noncomputable def rank (G : CFGraph) (D : CFDiv G) : ℤ :=
  Classical.choose (rank_exists G D)

/-- `rank_geq G D k` is equivalent to `rank G D ≥ k`. -/
lemma rank_geq_iff (G : CFGraph) (D : CFDiv G) (k : ℤ) :
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

/-- `rank_eq G D r` is equivalent to `rank G D = r`. -/
lemma rank_eq_iff (G : CFGraph) (D : CFDiv G) (r : ℤ) :
  rank_eq G D r ↔ rank G D = r := by
  dsimp [rank_eq]
  have split_eq x: x = r ↔ (x ≥ r ∧ ¬(x ≥ r + 1)) := by
    rw [not_le]
    rw [Int.lt_add_one_iff]
    have helper := @le_antisymm_iff _ _ x r
    rw [helper, and_comm]
  rw [split_eq (rank G D)]
  rw [rank_geq_iff G D r, rank_geq_iff G D (r+1)]

/-- Lemma: If a divisor is winnable, there exists an effective divisor linearly equivalent to it -/
lemma winnable_iff_exists_effective (G : CFGraph) (D : CFDiv G) :
  winnable G D ↔ ∃ D' : CFDiv G, effective D' ∧ linear_equiv G D D' := by
  unfold winnable Eff
  simp

/-- Lemma: Helper for rank characterization to get effective divisor -/
lemma rank_get_effective (G : CFGraph) (D : CFDiv G) :
  ∃ E : CFDiv G, effective E ∧ deg E = rank G D + 1 ∧ ¬(winnable G (D-E)) := by
  have h : rank_eq G D (rank G D) := by rw [rank_eq_iff]
  rcases h with ⟨_, h_r_not_geq⟩
  dsimp [rank_geq] at h_r_not_geq
  push Not at h_r_not_geq
  rcases h_r_not_geq with ⟨E, ⟨h_E_eff, h_E_deg⟩, h_E_not_winnable⟩
  exact ⟨E, h_E_eff, h_E_deg, h_E_not_winnable⟩

/-- Helpful corollary: rank = -1 exactly when divisor is not winnable -/
lemma rank_neg_one_iff_unwinnable (G : CFGraph) (D : CFDiv G) :
  rank G D = -1 ↔ ¬(winnable G D) := by
  have h := rank_eq_neg_one_iff_unwinnable  G D
  have h_spec := Classical.choose_spec (rank_exists G D)
  let r := rank G D
  have h_r : rank_eq G D r := h_spec
  constructor
  · intro hr
    have h₁ : r = -1 := hr
    rw [h₁] at h_r
    exact h.mp h_r
  · intro hwin
    exact rank_unique G D r (-1) h_r (h.mpr hwin)

/-- Lemma: If rank is not non-negative, then it equals -1 -/
lemma rank_neg_one_of_not_nonneg (G : CFGraph) (D : CFDiv G) (h_not_nonneg : ¬(rank G D ≥ 0)) : rank G D = -1 := by
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
lemma rank_geq_neg_one (G : CFGraph) (D : CFDiv G) : rank G D ≥ -1 := by
  by_contra h
  have h_not_nonneg : ¬(rank G D ≥ 0) := by
    intro h_contra
    linarith
  have h_rank_neg_one := rank_neg_one_of_not_nonneg G D h_not_nonneg
  linarith

/-- The rank of the zero divisor is zero. -/
lemma zero_divisor_rank (G : CFGraph) : rank G (0:CFDiv G) = 0 := by
  rw [← rank_eq_iff]
  constructor
  have h_eff : effective (0:CFDiv G) := by
    simp [effective]
  rw [rank_nonneg_iff_winnable G (0:CFDiv G)]
  exact winnable_of_effective G (0:CFDiv G) h_eff
  have ineq := rank_le_degree G (0:CFDiv G) 1 (by norm_num)
  simp [deg] at ineq
  exact ineq
