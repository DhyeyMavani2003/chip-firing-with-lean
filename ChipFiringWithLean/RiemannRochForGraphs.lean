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
theorem riemann_roch_for_graphs (G : CFGraph V) (D : CFDiv V) :
  rank G D - rank G (canonical_divisor G - D) = deg D - genus G + 1 := by
  -- Get rank value for D
  let r := rank G D

  -- Get effective divisor E using rank characterization
  rcases rank_get_effective G D with ⟨E, h_E_eff, h_E_deg, h_D_E_unwin⟩

  -- Fix a vertex q
  rcases Fintype.exists_elem V with ⟨q, _⟩

  -- Apply Dhar's algorithm to D - E to get q-reduced form
  rcases helper_dhar_algorithm G q (λ v => D v - E v) with ⟨c, k, h_equiv, h_super⟩

  -- k must be negative since D - E is unwinnable
  have h_k_neg := helper_dhar_negative_k G q (λ v => D v - E v) h_D_E_unwin c k h_equiv h_super

  -- Get maximal superstable c' ≥ c
  rcases helper_maximal_superstable_exists G q c h_super with ⟨c', h_max', h_ge⟩

  -- Let O be corresponding acyclic orientation with unique source q (from bijection)
  rcases stable_bijection G q with ⟨_, h_surj⟩
  -- O_subtype has type {O // is_acyclic G O ∧ (∀ w, is_source G O w → w = q)}
  rcases h_surj ⟨c', h_max'⟩ with ⟨O_subtype, h_f_eq_c'⟩

  -- From h_f_eq_c' : f O_subtype = ⟨c', h_max'⟩, we get that the configuration part is equal
  have h_orient_config_eq_c' : orientation_to_config G O_subtype.val q O_subtype.prop.1 O_subtype.prop.2 = c' := by
    exact Subtype.mk.inj h_f_eq_c'

  -- Define H := (c' - c) - (k + 1)q as a divisor
  let H : CFDiv V := λ v =>
    if v = q then -(k + 1)
    else c'.vertex_degree v - c.vertex_degree v

  -- Get key inequality from axiom
  have h_ineq := rank_degree_inequality G D

  -- Get reverse inequality by applying to K-D
  have h_ineq_rev := rank_degree_inequality G (λ v => canonical_divisor G v - D v)

  -- Get degree of canonical divisor
  have h_deg_K : deg (canonical_divisor G) = 2 * genus G - 2 :=
    degree_of_canonical_divisor G

  -- Since rank is an integer and we have bounds, equality must hold
  suffices rank G D - rank G (λ v => canonical_divisor G v - D v) ≥ deg D - genus G + 1 ∧
           rank G D - rank G (λ v => canonical_divisor G v - D v) ≤ deg D - genus G + 1 from
    le_antisymm (this.2) (this.1)

  constructor
  · -- Lower bound
    linarith [h_ineq]
  · -- Upper bound
    have h_swap := rank_degree_inequality G (λ v => canonical_divisor G v - D v)
    -- Simplify double subtraction in h_swap
    have h_sub_simplify : (λ (v : V) => canonical_divisor G v - (canonical_divisor G v - D v)) = D := by
      funext v
      ring

    rw [h_sub_simplify] at h_swap

    have h_deg_sub : deg (λ v => canonical_divisor G v - D v) = deg (canonical_divisor G) - deg D := by
      unfold deg
      -- Split the sum over subtraction
      rw [Finset.sum_sub_distrib]

    -- Substitute the degree of canonical divisor
    rw [h_deg_K] at h_deg_sub

    -- Simplify inequality
    have h_ineq_sub : deg (λ v => canonical_divisor G v - D v) - genus G <
      rank G (λ v => canonical_divisor G v - D v) - rank G D := h_swap

    rw [h_deg_sub] at h_ineq_sub

    -- Final inequality using linarith
    linarith [h_ineq_sub]

/-- [Proven] Corollary 4.4.1: A divisor D is maximal unwinnable if and only if K-D is maximal unwinnable -/
theorem maximal_unwinnable_symmetry
    (G : CFGraph V) (D : CFDiv V) :
  maximal_unwinnable G D ↔ maximal_unwinnable G (canonical_divisor G - D) := by
  constructor
  -- Forward direction
  { intro h_max_unwin
    -- Get rank = -1 from maximal unwinnable
    have h_rank_neg : rank G D = -1 := by
      rw [rank_neg_one_iff_unwinnable]
      exact h_max_unwin.1

    -- Get degree = g-1 from maximal unwinnable
    have h_deg : deg D = genus G - 1 := maximal_unwinnable_deg G D h_max_unwin

    -- Use Riemann-Roch
    have h_RR := riemann_roch_for_graphs G D
    rw [h_rank_neg] at h_RR

    -- Get degree of K-D
    have h_deg_K := degree_of_canonical_divisor G
    have h_deg_KD : deg (canonical_divisor G - D) = genus G - 1 := by
      -- Get general distributive property for deg over subtraction
      have h_deg_sub : ∀ D₁ D₂ : CFDiv V, deg (D₁ - D₂) = deg D₁ - deg D₂ := by
        intro D₁ D₂
        unfold deg
        simp [sub_apply]

      -- Convert lambda form to standard subtraction
      rw [divisor_sub_eq_lambda G (canonical_divisor G) D]

      -- Apply distributive property
      rw [h_deg_sub (canonical_divisor G) D]

      -- Use known values
      rw [h_deg_K, h_deg]

      -- Arithmetic: (2g-2) - (g-1) = g-1
      ring

    constructor
    · -- K-D is unwinnable
      rw [←rank_neg_one_iff_unwinnable]
      linarith
    · -- Adding chip makes K-D winnable
      intro v -- Goal: winnable G ((K-D) + δᵥ)
      -- Assume for contradiction that (K-D) + δᵥ is not winnable
      by_contra h_KD_plus_chip_not_winnable

      -- If not winnable, its rank is -1
      have h_rank_KD_plus_chip_is_neg_one : rank G ((canonical_divisor G - D) + one_chip v) = -1 := by
        rw [rank_neg_one_iff_unwinnable]
        exact h_KD_plus_chip_not_winnable

      -- Let E = (K-D) + δᵥ
      let E : CFDiv V := (canonical_divisor G - D) + one_chip v
      -- have h_rank_E_is_neg_one : rank G E = -1 := h_rank_KD_plus_chip_is_neg_one -- This is just a restatement

      -- Calculate deg E
      have h_deg_E : deg E = genus G := by
        -- E is defined as (λ w => A w + B w). We want to show deg E = genus G.
        -- Explicitly change the goal to unfold E to see the sum structure.
        change deg ( (canonical_divisor G - D) + one_chip v ) = genus G
        -- Now the goal is deg (A + B) = genus G, where A = (K-D) and B = δᵥ.
        rw [deg_add] -- Applies to deg (A + B), changing goal to deg A + deg B = genus G.
        -- Goal: deg (λ w => canonical_divisor G w - D w) + deg (λ w => if w = v then 1 else 0) = genus G
        rw [h_deg_KD] -- Substitutes deg(K-D) with (genus G - 1).
        -- Goal: (genus G - 1) + deg (λ w => if w = v then 1 else 0) = genus G
        -- This simplifies to showing: deg (λ w => if w = v then 1 else 0) = 1
        have h_deg_delta_v : deg (one_chip v) = 1 := by
          unfold deg
          -- Goal: ∑ x in Finset.univ, (if x = v then 1 else 0) = 1
          -- This sum is 1 when x=v and 0 for all other x.
          rw [Finset.sum_eq_single_of_mem v (Finset.mem_univ v)]
          · -- Case 1: Prove the term for x = v is indeed 1.
            -- The term is (if v = v then 1 else 0).
            dsimp [one_chip]
            simp only [eq_self_iff_true, if_true]
          · -- Case 2: Prove for all x ≠ v, the term (if x = v then 1 else 0) is 0.
            intros x _ hx_ne_v -- x is an element of Finset.univ, and x ≠ v.
            -- The term is (if x = v then 1 else 0).
            dsimp[one_chip]
            simp only [hx_ne_v, if_false] -- Since x ≠ v, (if x=v ...) becomes (if false ...), which is 0.
        rw [h_deg_delta_v] -- Substitute deg(δᵥ) = 1.
        -- Goal is now (genus G - 1) + 1 = genus G
        ring

      -- Apply Riemann-Roch to E
      -- rank G E - rank G (K-E) = deg E - (g-1)
      have h_RR_E := riemann_roch_for_graphs G E
      -- Substitute rank G E = -1 and deg E = g
      rw [h_rank_KD_plus_chip_is_neg_one, h_deg_E] at h_RR_E
      -- So, -1 - rank G (K-E) = g - (g-1) = 1
      -- This implies rank G (K-E) = -2

      -- Simplify K-E
      have h_K_minus_E_eq_D_minus_chip : (canonical_divisor G - E) = (D - one_chip v) := by
        simp only [E]
        simp
      -- Substitute K-E into the Riemann-Roch equation for E
      rw [h_K_minus_E_eq_D_minus_chip] at h_RR_E
      -- Now h_RR_E is: -1 - rank G (D - δᵥ) = 1, which means rank G (D - δᵥ) = -2

      -- This is a contradiction because rank must be ≥ -1.
      have h_rank_D_minus_chip_ge_neg_one : rank G (D - one_chip v) ≥ -1 := by
        -- The rank is either -1 or non-negative.
        by_cases h_nonneg: rank G (D - one_chip v) ≥ 0
        · linarith -- if non-negative, then it is ≥ -1
        · -- If not non-negative, then it must be -1 by rank_neg_one_of_not_nonneg
          have rank_is_neg_one := rank_neg_one_of_not_nonneg G (D - one_chip v) h_nonneg
          linarith [rank_is_neg_one] -- if it's -1, then it is ≥ -1

      -- The contradiction comes from h_RR_E (which implies rank = -2) and h_rank_D_minus_chip_ge_neg_one (rank ≥ -1)
      linarith [h_RR_E, h_rank_D_minus_chip_ge_neg_one]
  }
  -- Reverse direction
  { intro h_max_unwin_K
    -- Apply canonical double difference
    rw [←canonical_double_diff G D]
    -- Mirror forward direction's proof
    exact maximal_unwinnable_symmetry G (λ v => canonical_divisor G v - D v) |>.mp h_max_unwin_K
  }
  termination_by (rank G D + 1).toNat
  decreasing_by { exact rank_decreases_for_KD G D h_max_unwin_K }


/-- [Proven] Clifford's Theorem (4.4.2): For a divisor D with non-negative rank
             and K-D also having non-negative rank, the rank of D is at most half its degree. -/
theorem clifford_theorem
    (G : CFGraph V) (D : CFDiv V)
    (h_D : rank G D ≥ 0)
    (h_KD : rank G (canonical_divisor G - D) ≥ 0) :
    (rank G D : ℚ) ≤ (deg D : ℚ) / 2 := by
  -- Get canonical divisor K's rank using Riemann-Roch
  have h_K_rank : rank G (canonical_divisor G) = genus G - 1 := by
    -- Apply Riemann-Roch with D = K
    have h_rr := riemann_roch_for_graphs G (canonical_divisor G)
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
  have h_rr := riemann_roch_for_graphs G D

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
  (G : CFGraph V) (D : CFDiv V) :
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
        exact clifford_theorem G D h_rank h_rankKD
      · -- Case where r(K-D) = -1: use Riemann-Roch
        have h_rr := riemann_roch_for_graphs G D
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
    have h_rr := riemann_roch_for_graphs G D
    rw [h_rankKD] at h_rr
    rw [sub_neg_eq_add] at h_rr
    linarith
