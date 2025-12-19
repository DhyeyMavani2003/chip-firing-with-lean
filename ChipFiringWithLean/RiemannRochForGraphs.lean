import ChipFiringWithLean.Basic
import ChipFiringWithLean.Config
import ChipFiringWithLean.Orientation
import ChipFiringWithLean.Rank
import ChipFiringWithLean.RRGHelpers
import Mathlib.Algebra.Ring.Int
import Paperproof

set_option linter.unusedVariables false
set_option trace.split.failure true

open Multiset Finset

-- Assume V is a finite type with decidable equality
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]

/-- [Proven] The main Riemann-Roch theorem for graphs -/
theorem riemann_roch_for_graphs {G : CFGraph V} (h_conn : graph_connected G) (D : CFDiv V) :
  rank G D - rank G (canonical_divisor G - D) = deg D - genus G + 1 := by
  let K := canonical_divisor G

  -- Get key inequality
  have h_ineq := rank_degree_inequality h_conn D

  -- Get reverse inequality by applying to K-D
  have h_ineq_rev := rank_degree_inequality h_conn (K-D)

  -- Get degree of canonical divisor
  have h_deg_K : deg (canonical_divisor G) = 2 * genus G - 2 :=
    degree_of_canonical_divisor G

  -- Since rank is an integer and we have bounds, equality must hold
  suffices rank G D - rank G (K-D) ≥ deg D - genus G + 1 ∧
           rank G D - rank G (K-D) ≤ deg D - genus G + 1 from
    le_antisymm (this.2) (this.1)

  constructor
  · -- Lower bound
    linarith
  · -- Upper bound
    rw [deg.map_sub, h_deg_K] at h_ineq_rev
    have : canonical_divisor G - (K-D) = D := by
      rw [sub_sub_self]
    rw [this] at h_ineq_rev
    linarith

/-- [Proven] Corollary 4.4.1: A divisor D is maximal unwinnable if and only if K-D is maximal unwinnable -/
theorem maximal_unwinnable_symmetry
    {G : CFGraph V} (h_conn : graph_connected G) (D : CFDiv V) :
  maximal_unwinnable G D ↔ maximal_unwinnable G (canonical_divisor G - D) := by
  set K := canonical_divisor G with K_def
  suffices : ∀ (D : CFDiv V), maximal_unwinnable G D → maximal_unwinnable G (canonical_divisor G - D)
  . constructor
    exact this D
    intro h
    apply this (K-D) at h
    rw [sub_sub_self] at h
    exact h
  -- Now we can just prove the forward direction
  intro D
  intro h_max_unwin
  -- Get rank = -1 from maximal unwinnable
  have h_rank_neg : rank G D = -1 := by
    rw [rank_neg_one_iff_unwinnable]
    exact h_max_unwin.1

  -- Get degree = g-1 from maximal unwinnable
  have h_deg : deg D = genus G - 1 := maximal_unwinnable_deg h_conn D h_max_unwin

  -- Use Riemann-Roch
  have h_RR := riemann_roch_for_graphs h_conn D
  rw [h_rank_neg] at h_RR

  -- Get degree of K-D
  have h_deg_K := degree_of_canonical_divisor G
  have h_deg_KD : deg (canonical_divisor G - D) = genus G - 1 := by
    rw [deg.map_sub]
    rw [h_deg_K, h_deg]
    linarith

  constructor
  · -- K-D is unwinnable
    rw [←rank_neg_one_iff_unwinnable]
    linarith
  · -- Adding chip makes K-D winnable
    intro v -- Goal: winnable G ((K-D) + δᵥ)
    -- Let E = (K-D) + δᵥ
    set E : CFDiv V := (canonical_divisor G - D) + one_chip v with E_def
    suffices : winnable G E
    . exact this
    -- To show E is winnable, we will use Riemann-Roch on E
    have h_deg_E : deg E = genus G := by
      rw [E_def, deg.map_add, deg_one_chip, h_deg_KD]
      linarith
    apply (rank_nonneg_iff_winnable G E).mp
    rw [rank_geq_iff G E]
    calc
      rank G E = rank G (K-E) + deg E +1 - genus G := by
        linarith [riemann_roch_for_graphs h_conn E]
      _ ≥ deg E - genus G := by
        linarith [rank_geq_neg_one G (K - E)]
      _ = 0 := by linarith[h_deg_E]

/-- [Proven] Clifford's Theorem (4.4.2): For a divisor D with non-negative rank
             and K-D also having non-negative rank, the rank of D is at most half its degree. -/
theorem clifford_theorem
    {G : CFGraph V} (h_conn : graph_connected G) (D : CFDiv V)
    (h_D : rank G D ≥ 0)
    (h_KD : rank G (canonical_divisor G - D) ≥ 0) :
    (rank G D : ℚ) ≤ (deg D : ℚ) / 2 := by
  -- Get canonical divisor K's rank using Riemann-Roch
  have h_K_rank : rank G (canonical_divisor G) = genus G - 1 := by
    -- Apply Riemann-Roch with D = K
    have h_rr := riemann_roch_for_graphs h_conn (canonical_divisor G)
    -- For K-K = 0, rank is 0
    have h_K_minus_K : rank G (canonical_divisor G - canonical_divisor G) = 0 := by
      -- Show that this divisor is the zero divisor
      have h1 : (canonical_divisor G - canonical_divisor G) = 0 := by
        simp
      -- Show that the zero divisor has rank 0
      have h2 : rank G 0 = 0 := zero_divisor_rank G
      -- Substitute back
      rw [h1, h2]
    -- Substitute into Riemann-Roch
    rw [h_K_minus_K] at h_rr
    -- Use degree_of_canonical_divisor
    rw [degree_of_canonical_divisor] at h_rr
    -- Solve for rank G K
    linarith

  -- Apply rank subadditivity
  have h_subadd := rank_subadditive G D (canonical_divisor G - D) h_D h_KD
  -- The sum D + (K-D) = K
  have h_sum : (D + (canonical_divisor G - D)) = canonical_divisor G := by
    funext v
    simp
  rw [h_sum] at h_subadd
  rw [h_K_rank] at h_subadd

  -- Use Riemann-Roch to get r(K-D) in terms of r(D)
  have h_rr := riemann_roch_for_graphs h_conn D

  -- Explicit algebraic manipulation
  have h1 : rank G (canonical_divisor G - D) =
           rank G D - (deg D - genus G + 1) := by
    linarith

  -- Substitute this into the subadditivity inequality
  have h2 : genus G - 1 ≥ rank G D + (rank G D - (deg D - genus G + 1)) := by
    rw [h1] at h_subadd
    exact h_subadd

  -- Solve for rank G D
  have h3 : 2 * rank G D - (deg D - genus G + 1) ≤ genus G - 1 := by
    linarith

  have h4 : 2 * rank G D ≤ deg D := by
    linarith

  have h5 : (rank G D : ℚ) ≤ (deg D : ℚ) / 2 := by
    -- Convert to rational numbers and use algebraic properties
    have h_cast : (2 : ℚ) * (rank G D : ℚ) ≤ (deg D : ℚ) := by
      -- Cast integer inequality to rational
      exact_mod_cast h4

    -- Divide both sides by 2 directly using algebra
    have h_two_pos : (0 : ℚ) < 2 := by norm_num

    calc (rank G D : ℚ)
      _  = (rank G D : ℚ) * (1 : ℚ) := by ring
      _  = (rank G D : ℚ) * (2 / 2 : ℚ) := by norm_num
      _  = (2 : ℚ) * (rank G D : ℚ) / 2 := by field_simp
      _  ≤ (deg D : ℚ) / 2 := by
          -- Use the fact that division by positive number preserves inequality
          apply (div_le_div_right h_two_pos).mpr
          exact h_cast

  exact h5

/-- [Proven] RRG's Corollary 4.4.3 establishing divisor degree to rank correspondence  -/
theorem riemann_roch_deg_to_rank_corollary
  {G : CFGraph V} (h_conn : graph_connected G) (D : CFDiv V) :
  -- Part 1
  (deg D < 0 → rank G D = -1) ∧
  -- Part 2
  (0 ≤ (deg D : ℚ) ∧ (deg D : ℚ) ≤ 2 * (genus G : ℚ) - 2 → (rank G D : ℚ) ≤ (deg D : ℚ) / 2) ∧
  -- Part 3
  (deg D > 2 * genus G - 2 → rank G D = deg D - genus G) := by
  constructor
  · -- Part 1: deg(D) < 0 implies r(D) = -1
    intro h_deg_neg
    rw [rank_neg_one_iff_unwinnable]
    intro h_winnable
    -- Use winnable_iff_exists_effective
    obtain ⟨D', h_eff, h_equiv⟩ := winnable_iff_exists_effective G D |>.mp h_winnable
    -- Linear equivalence preserves degree
    have h_deg_eq : deg D = deg D' := by
      exact linear_equiv_preserves_deg G D D' h_equiv
    -- Effective divisors have non-negative degree
    have h_D'_nonneg : deg D' ≥ 0 := by
      exact effective_nonneg_deg D' h_eff
    -- Contradiction: D has negative degree but is equivalent to non-negative degree divisor
    rw [←h_deg_eq] at h_D'_nonneg
    exact not_le_of_gt h_deg_neg h_D'_nonneg

  constructor
  · -- Part 2: 0 ≤ deg(D) ≤ 2g-2 implies r(D) ≤ deg(D)/2
    intro ⟨h_deg_nonneg, h_deg_upper⟩
    by_cases h_rank : rank G D ≥ 0
    · -- Case where r(D) ≥ 0
      let K := canonical_divisor G
      by_cases h_rankKD : rank G (K - D) ≥ 0
      · -- Case where r(K-D) ≥ 0: use Clifford's theorem
        exact clifford_theorem h_conn D h_rank h_rankKD
      · -- Case where r(K-D) = -1: use Riemann-Roch
        have h_rr := riemann_roch_for_graphs h_conn D
        have h_rankKD_eq : rank G (K - D) = -1 :=
          rank_neg_one_of_not_nonneg G (K - D) h_rankKD

        rw [h_rankKD_eq] at h_rr

        -- Arithmetic manipulation to get r(D) equality
        have this : rank G D = deg D - genus G := by
          -- Convert h_rr from (rank G D - (-1)) to (rank G D + 1)
          rw [sub_neg_eq_add] at h_rr
          have := calc
            rank G D = rank G D + 1 - 1 := by ring
            _ = deg D - genus G + 1 - 1 := by rw [h_rr]
            _ = deg D - genus G := by ring
          exact this

        -- Apply the result
        rw [this]

        -- Show that deg D - genus G ≤ deg D / 2 using rational numbers
        have h_bound : (deg D - genus G : ℚ) ≤ (deg D : ℚ) / 2 := by
          linarith [h_deg_upper]

        -- Make sure types match with explicit cast
        have h_cast : (deg D - genus G : ℚ) = (↑(deg D - genus G) : ℚ) := by
          exact_mod_cast rfl
        rw [← h_cast]
        exact h_bound

    · -- Case where r(D) < 0
      have h_rank_eq := rank_neg_one_of_not_nonneg G D h_rank
      have h_bound : -1 ≤ deg D / 2 := by
        -- The division by 2 preserves non-negativity for deg D
        have h_div_nonneg : deg D / 2 ≥ 0 := by
          have h_two_pos : (2 : ℤ) > 0 := by norm_num
          rw [Int.div_nonneg_iff_of_pos h_two_pos]
          -- Convert explicitly to the right type
          have h : deg D ≥ 0 := by exact_mod_cast h_deg_nonneg
          exact h

        linarith
      rw [h_rank_eq]

      -- Convert to rational numbers
      have h_bound_rat : ((-1) : ℚ) ≤ (deg D : ℚ) / 2 := by linarith [h_bound]

      exact h_bound_rat

  · -- Part 3: deg(D) > 2g-2 implies r(D) = deg(D) - g
    intro h_deg_large
    have h_canon := degree_of_canonical_divisor G
    -- Show K-D has negative degree
    have h_KD_neg : deg (λ v => canonical_divisor G v - D v) < 0 := by
      -- Calculate deg(K-D)
      calc
        deg (λ v => canonical_divisor G v - D v)
        _ = deg (canonical_divisor G) - deg D := by
          unfold deg
          simp [sub_apply]
        _ = 2 * genus G - 2 - deg D := by rw [h_canon]
        _ < 0 := by linarith

    -- Show K-D is unwinnable, so rank = -1
    have h_rankKD : rank G (canonical_divisor G - D) = -1 := by
      rw [rank_neg_one_iff_unwinnable]
      intro h_win
      -- If winnable, would be linearly equivalent to effective divisor
      obtain ⟨E, h_eff, h_equiv⟩ := winnable_iff_exists_effective G _ |>.mp h_win
      have h_deg_eq := linear_equiv_preserves_deg G _ E h_equiv
      -- But effective divisors have non-negative degree
      have h_E_nonneg := effective_nonneg_deg E h_eff
      rw [←h_deg_eq] at h_E_nonneg
      -- Contradiction: K-D has negative degree
      exact not_le_of_gt h_KD_neg h_E_nonneg

    -- Apply Riemann-Roch to get r(D) = deg(D) - g
    have h_rr := riemann_roch_for_graphs h_conn D
    rw [h_rankKD] at h_rr
    rw [sub_neg_eq_add] at h_rr
    linarith
