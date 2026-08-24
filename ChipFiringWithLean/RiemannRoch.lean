import ChipFiringWithLean.RRGHelpers

set_option linter.unusedVariables false
set_option trace.split.failure true

open Multiset Finset

theorem riemann_roch_for_graphs {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) :
  rank G D - rank G (canonical_divisor G - D) = deg D - genus G + 1 := by
  set K := canonical_divisor G with K_eq
  have h_ineq := rank_degree_inequality h_conn D
  have h_ineq_rev : deg (K-D) - genus G < rank G (K-D) - rank G D := by
    convert rank_degree_inequality h_conn (K-D)
    abel
  have deg_sub : deg (K-D) = deg K - deg D := by rw [deg.map_sub]
  have h_deg_K : deg (canonical_divisor G) = 2 * genus G - 2 := degree_of_canonical_divisor G
  linarith

private lemma rank_subadditive (G : CFGraph) (D D' : CFDiv G)
    (h_D : rank G D ≥ 0) (h_D' : rank G D' ≥ 0) :
    rank G (D+D') ≥ rank G D + rank G D' := by
  obtain ⟨k₁, h_k₁⟩ : ∃ k : ℕ, (k : ℤ) = rank G D := ⟨_, Int.toNat_of_nonneg h_D⟩
  obtain ⟨k₂, h_k₂⟩ : ∃ k : ℕ, (k : ℤ) = rank G D' := ⟨_, Int.toNat_of_nonneg h_D'⟩
  have h_rank_geq : rank_geq G (D + D') (k₁ + k₂) := by
    rintro E'' ⟨h_eff, h_deg⟩
    obtain ⟨E₁, E₂, h_E₁_eff, h_E₂_eff, h_E₁_deg, h_E₂_deg, h_sum⟩ :=
      effective_divisor_decomposition G E'' k₁ k₂ h_eff h_deg
    have h_D_win := (rank_geq_iff G D k₁).mpr (le_of_eq h_k₁) E₁ ⟨h_E₁_eff, h_E₁_deg⟩
    have h_D'_win := (rank_geq_iff G D' k₂).mpr (le_of_eq h_k₂) E₂ ⟨h_E₂_eff, h_E₂_deg⟩
    rw [h_sum]
    have h := winnable_add_winnable G (D-E₁) (D'-E₂) h_D_win h_D'_win
    rw [show D - E₁ + (D' - E₂) = (D + D') - (E₁ + E₂) by abel] at h
    exact h
  have h_final := (rank_geq_iff G (D+D') (k₁+k₂)).mp h_rank_geq
  linarith

theorem clifford_theorem
    {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G)
    (h_D : rank G D ≥ 0)
    (h_KD : rank G (canonical_divisor G - D) ≥ 0) :
    (rank G D : ℚ) ≤ (deg D : ℚ) / 2 := by
  have h_K_rank : rank G (canonical_divisor G) = genus G - 1 := by
    have h_rr := riemann_roch_for_graphs h_conn (canonical_divisor G)
    have h_K_minus_K : rank G (canonical_divisor G - canonical_divisor G) = 0 := by
      have h1 : (canonical_divisor G - canonical_divisor G) = 0 := by
        simp only [sub_self]
      have h2 : rank G 0 = 0 := zero_divisor_rank G
      rw [h1, h2]
    rw [h_K_minus_K] at h_rr
    rw [degree_of_canonical_divisor] at h_rr
    linarith
  have h_subadd := rank_subadditive G D (canonical_divisor G - D) h_D h_KD
  have h_sum : (D + (canonical_divisor G - D)) = canonical_divisor G := by
    funext v
    simp only [Pi.add_apply, Pi.sub_apply, add_sub_cancel]
  rw [h_sum] at h_subadd
  rw [h_K_rank] at h_subadd
  have h_rr := riemann_roch_for_graphs h_conn D
  have h_two : 2 * rank G D ≤ deg D := by linarith
  have h_two' : (2 : ℚ) * (rank G D : ℚ) ≤ (deg D : ℚ) := by exact_mod_cast h_two
  linarith
