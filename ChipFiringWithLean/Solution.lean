import ChipFiringWithLean.RiemannRoch

namespace Propositions

private lemma rank_unique (G : CFGraph) (D : CFDiv G) :
    ∀ r₁ r₂ : ℤ, rank_eq G D r₁ → rank_eq G D r₂ → r₁ = r₂ := by
  rintro r₁ r₂ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
  have hlt₁ : r₁ < r₂ + 1 := lt_of_rank_geq_not G D r₁ (r₂ + 1) h₁ h₂'
  have hlt₂ : r₂ < r₁ + 1 := lt_of_rank_geq_not G D r₂ (r₁ + 1) h₂ h₁'
  linarith

private lemma rank_spec (G : CFGraph) (D : CFDiv G) : rank_eq G D (rank G D) :=
  Classical.choose_spec (rank_exists G D)

theorem rank_well_defined (G : CFGraph) (D : CFDiv G) :
    (∃ r : ℤ, rank_eq G D r) ∧
      ∀ r₁ r₂ : ℤ, rank_eq G D r₁ → rank_eq G D r₂ → r₁ = r₂ := by
  exact ⟨rank_exists G D, rank_unique G D⟩

theorem riemann_roch {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) :
    ∀ r rdual : ℤ, rank_eq G D r → rank_eq G (canonical_divisor G - D) rdual →
      r - rdual = deg D + 1 - genus G := by
  intro r rdual h_rank h_rankdual
  have hr : rank G D = r := rank_unique G D (rank G D) r (rank_spec G D) h_rank
  have hrdual : rank G (canonical_divisor G - D) = rdual :=
    rank_unique G (canonical_divisor G - D) (rank G (canonical_divisor G - D)) rdual
      (rank_spec G (canonical_divisor G - D)) h_rankdual
  have h_rr := riemann_roch_for_graphs h_conn D
  rw [hr, hrdual] at h_rr
  linarith

theorem clifford {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) :
    ∀ r rdual : ℤ, rank_eq G D r → rank_eq G (canonical_divisor G - D) rdual →
      0 ≤ r → 0 ≤ rdual → (r : ℚ) ≤ (deg D : ℚ) / 2 := by
  intro r rdual h_rank h_rankdual hr_nonneg hrdual_nonneg
  have hr : rank G D = r := rank_unique G D (rank G D) r (rank_spec G D) h_rank
  have hrdual : rank G (canonical_divisor G - D) = rdual :=
    rank_unique G (canonical_divisor G - D) (rank G (canonical_divisor G - D)) rdual
      (rank_spec G (canonical_divisor G - D)) h_rankdual
  have h_clifford := clifford_theorem h_conn D (by simpa [hr] using hr_nonneg)
    (by simpa [hrdual] using hrdual_nonneg)
  rw [hr] at h_clifford
  exact h_clifford

end Propositions
