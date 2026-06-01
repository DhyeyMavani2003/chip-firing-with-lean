import ChipFiringWithLean.RRGHelpers
import Mathlib

-- import Paperproof

set_option linter.unusedVariables false
set_option trace.split.failure true

universe u

open Multiset Finset

/-!
# Riemann-Roch for graphs

The Riemann-Roch theorem for graphs and its main corollaries,
following [Corry-Perkinson], Chapter 5.

- `riemann_roch_for_graphs`: The Riemann-Roch theorem, $r(D) - r(K_G - D) = \deg(D) - g + 1$
  ([Corry-Perkinson], Theorem 5.9).
- `maximal_unwinnable_symmetry`: $D$ is maximal unwinnable iff $K_G - D$ is
  ([Corry-Perkinson], Corollary 5.11).
- `clifford_theorem`: If $r(D) \geq 0$ and $r(K_G - D) \geq 0$, then $r(D) \leq \deg(D)/2$
  ([Corry-Perkinson], Corollary 5.13).
- `riemann_roch_deg_to_rank_corollary`: Nonspecial range results
  ([Corry-Perkinson], Corollary 5.14).
-/

/-- **Riemann-Roch theorem for graphs:** $r(D) - r(K_G - D) = \deg(D) - g + 1$.
This is [Corry-Perkinson], Theorem 5.9. -/
theorem riemann_roch_for_graphs {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) :
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

/-- $D$ is maximal unwinnable if and only if $K_G - D$ is maximal unwinnable.
This is [Corry-Perkinson], Corollary 5.11. -/
theorem maximal_unwinnable_symmetry
    {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) :
  maximal_unwinnable G D ↔ maximal_unwinnable G (canonical_divisor G - D) := by
  set K := canonical_divisor G with K_def
  suffices ∀ (D : CFDiv G), maximal_unwinnable G D → maximal_unwinnable G (canonical_divisor G - D) by
    constructor
    exact this D
    intro h
    apply this (K-D) at h
    rw [sub_sub_self] at h
    exact h
  -- Now we can just prove the forward direction
  intro D h_max_unwin
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
    set E : CFDiv G := (canonical_divisor G - D) + one_chip v with E_def
    suffices winnable G E by
      exact this
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

/-- Rank of divisors is subadditive. -/
private lemma rank_subadditive (G : CFGraph) (D D' : CFDiv G)
    (h_D : rank G D ≥ 0) (h_D' : rank G D' ≥ 0) :
    rank G (D+D') ≥ rank G D + rank G D' := by
  -- Convert ranks to natural numbers
  let k₁ := (rank G D).toNat
  let k₂ := (rank G D').toNat

  -- Show rank is ≥ k₁ + k₂ by proving rank_geq
  have h_rank_geq : rank_geq G (D + D') (k₁ + k₂) := by
    -- Take any effective divisor E'' of degree k₁ + k₂
    intro E'' h_E''
    have ⟨h_eff, h_deg⟩ := h_E''

    -- Decompose E'' into E₁ and E₂ of degrees k₁ and k₂
    have ⟨E₁, E₂, h_E₁_eff, h_E₂_eff, h_E₁_deg, h_E₂_deg, h_sum⟩ :=
      helper_divisor_decomposition G E'' k₁ k₂ h_eff h_deg

    -- Convert our nat-based hypotheses to ℤ-based ones
    have h_D_nat : rank G D ≥ ↑k₁ := by
      have h_conv : ↑((rank G D).toNat) = rank G D := Int.toNat_of_nonneg h_D
      rw [←h_conv]

    have h_D'_nat : rank G D' ≥ ↑k₂ := by
      have h_conv : ↑((rank G D').toNat) = rank G D' := Int.toNat_of_nonneg h_D'
      rw [←h_conv]

    -- Get rank_geq properties
    have h_D_rank_geq : rank_geq G D k₁ := (rank_geq_iff G D k₁).mpr h_D_nat
    have h_D'_rank_geq : rank_geq G D' k₂ := (rank_geq_iff G D' k₂).mpr h_D'_nat

    -- Apply rank_geq to get winnability for both parts
    have h_D_win := h_D_rank_geq E₁ (by exact ⟨h_E₁_eff, h_E₁_deg⟩)
    have h_D'_win := h_D'_rank_geq E₂ (by exact ⟨h_E₂_eff, h_E₂_deg⟩)

    -- Show winnability of sum using helper_winnable_add and rearrangement
    rw [h_sum]
    have h := winnable_add_winnable G (D-E₁) (D'-E₂) h_D_win h_D'_win
    have h_arr : D - E₁ + (D' - E₂) = (D + D') - (E₁ + E₂) := by
      abel
    rw [h_arr] at h
    exact h

  -- Connect k₁, k₂ back to original ranks
  have h_k₁ : ↑k₁ = rank G D := by
    exact Int.toNat_of_nonneg h_D

  have h_k₂ : ↑k₂ = rank G D' := by
    exact Int.toNat_of_nonneg h_D'

  -- Show final inequality using transitivity
  have h_final := (rank_geq_iff G (D+D') (k₁+k₂)).mp h_rank_geq

  have h_sum : ↑(k₁ + k₂) = rank G D + rank G D' := by
    simp only [Nat.cast_add]  -- Use Nat.cast_add instead of Int.coe_add
    rw [h_k₁, h_k₂]

  linarith

/-- **Clifford's theorem:** If $r(D) \geq 0$ and $r(K_G - D) \geq 0$, then
$r(D) \leq \deg(D)/2$. This is [Corry-Perkinson], Corollary 5.13. -/
theorem clifford_theorem
    {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G)
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
    have h_cast : (2 : ℚ) * (rank G D : ℚ) ≤ (deg D : ℚ) := by
      exact_mod_cast h4
    linarith

  exact h5

/-- Nonspecial range: (1) $\deg(D) < 0 \Rightarrow r(D) = -1$; (2) $0 \leq \deg(D) \leq 2g-2
\Rightarrow r(D) \leq \deg(D)/2$; (3) $\deg(D) > 2g-2 \Rightarrow r(D) = \deg(D) - g$.
This is [Corry-Perkinson], Corollary 5.14. -/
theorem riemann_roch_deg_to_rank_corollary
  {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) :
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
      exact deg_of_eff_nonneg D' h_eff
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
          have h : deg D ≥ 0 := by exact_mod_cast h_deg_nonneg
          omega

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
          simp
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
      have h_E_nonneg := deg_of_eff_nonneg E h_eff
      rw [←h_deg_eq] at h_E_nonneg
      -- Contradiction: K-D has negative degree
      exact not_le_of_gt h_KD_neg h_E_nonneg

    -- Apply Riemann-Roch to get r(D) = deg(D) - g
    have h_rr := riemann_roch_for_graphs h_conn D
    rw [h_rankKD] at h_rr
    rw [sub_neg_eq_add] at h_rr
    linarith

/-!
## Gonality
The Riemann-Roch theorem provides some basic information about the *gonality* of a graph.
-/

def gonality_leq (G : CFGraph) (k : ℤ) : Prop := ∃ D : CFDiv G, rank G D ≥ 1 ∧ deg D = k

/-- `gonality_geq G k` means that no divisor of degree `< k` has rank at least `1`. -/
def gonality_geq (G : CFGraph) (k : ℤ) : Prop :=
  ∀ l : ℤ, l < k → ¬ gonality_leq G l

/-- A connected graph has gonality at most `g + 1`, where `g` is its genus. -/
theorem gonality_leq_genus_add_one
    {G : CFGraph} (h_conn : graph_connected G) : gonality_leq G (genus G + 1) := by
  let q : G.V := Classical.arbitrary G.V
  let D : CFDiv G := (genus G + 1) • one_chip q
  have h_deg_D : deg D = genus G + 1 := by
    dsimp [D]
    rw [map_zsmul, deg_one_chip, zsmul_one]
    simp
  have h_rank_geq : rank_geq G D 1 := by
    intro E hE
    dsimp [eff_of_degree] at hE
    rcases hE with ⟨hE_eff, hE_deg⟩
    have h_deg_sub : deg (D - E) = genus G := by
      rw [deg.map_sub, h_deg_D, hE_deg]
      ring
    apply winnable_of_deg_ge_genus h_conn (D - E)
    rw [h_deg_sub]
  refine ⟨D, (rank_geq_iff G D 1).mp h_rank_geq, h_deg_D⟩

/-- Any degree realizing `gonality_leq` is at least `1`. -/
theorem one_le_of_gonality_leq {G : CFGraph} {k : ℤ} (h_gon : gonality_leq G k) : 1 ≤ k := by
  rcases h_gon with ⟨D, h_rank, h_deg⟩
  have h_rank_geq : rank_geq G D 1 := (rank_geq_iff G D 1).mpr h_rank
  have h_deg_lower : (1 : ℤ) ≤ deg D := rank_le_degree G D 1 (by norm_num) h_rank_geq
  simpa [h_deg] using h_deg_lower

/-- The gonality of a connected graph is the smallest degree of a divisor of rank at least `1`. -/
noncomputable def gonality {G : CFGraph} (h_conn : graph_connected G) : ℤ :=
  sInf {k : ℤ | gonality_leq G k}

/-- A connected graph has gonality at most `g + 1`, where `g` is its genus. -/
private lemma gonality_le_genus_add_one {G : CFGraph} (h_conn : graph_connected G) :
    gonality h_conn ≤ genus G + 1 := by
  let S : Set ℤ := {k : ℤ | gonality_leq G k}
  have h_bdd : BddBelow S := by
    refine ⟨1, ?_⟩
    intro k hk
    exact one_le_of_gonality_leq hk
  dsimp [gonality, S]
  exact csInf_le h_bdd (gonality_leq_genus_add_one h_conn)

/-- The gonality of a connected graph is at least `1`. -/
private lemma gonality_ge_one {G : CFGraph} (h_conn : graph_connected G) : 1 ≤ gonality h_conn := by
  let S : Set ℤ := {k : ℤ | gonality_leq G k}
  have h_nonempty : S.Nonempty := by
    refine ⟨genus G + 1, ?_⟩
    exact gonality_leq_genus_add_one h_conn
  dsimp [gonality, S]
  refine le_csInf h_nonempty ?_
  intro k hk
  exact one_le_of_gonality_leq hk

@[simp] theorem gonality_geq_iff {G : CFGraph} (h_conn : graph_connected G) (k : ℤ) :
    gonality_geq G k ↔ gonality h_conn ≥ k := by
  let S : Set ℤ := {l : ℤ | gonality_leq G l}
  have h_nonempty : S.Nonempty := by
    refine ⟨genus G + 1, ?_⟩
    exact gonality_leq_genus_add_one h_conn
  have h_bdd : BddBelow S := by
    refine ⟨1, ?_⟩
    intro l hl
    exact one_le_of_gonality_leq hl
  constructor
  · intro h_geq
    dsimp [gonality, gonality_geq, S]
    refine le_csInf h_nonempty ?_
    intro l hl
    by_contra hlt
    have hlt' : l < k := by linarith
    exact h_geq l hlt' hl
  · intro h_gon l hl h_leq
    have h_inf_le : gonality h_conn ≤ l := by
      dsimp [gonality, S]
      exact csInf_le h_bdd h_leq
    linarith

/-!
## Conjectures and partial results

Baker's *Specialization of linear systems from curves to graphs* poses several conjectures
relating Brill–Noether theory of algebraic curves to chip-firing on graphs. Two of them are, at
the time of writing, **open problems**:

* the **Brill–Noether existence conjecture** for finite graphs (Conjecture 3.9(1)), and
* the **gonality conjecture** `gon(G) ≤ ⌊(g+3)/2⌋` (Conjecture 3.10(1)), which is exactly the
  `r = 1` case of the existence conjecture.

The existence conjecture is known only for genus `≤ 5` (Atanasov–Ranganathan) and is open even
for `r = 1`; the gonality conjecture has no known counterexample but no general proof. See
arXiv:2304.07405, arXiv:1609.02091, arXiv:1911.11514, and the survey context in
<https://arxiv.org/abs/2508.00269>.

Because these statements are genuinely open, we do **not** assert them as theorems (doing so
would require a `sorry` that can never be discharged). Instead this section:

* records the conjectures as named `Prop`s (`BrillNoetherExistence`, `GonalityConjecture`),
* proves the cases that *are* unconditionally provable from Riemann–Roch
  (`brill_noether_existence_rank_zero`, `brill_noether_existence_of_deg_ge`), and
* proves the conditional implications reducing the gonality statements to Brill–Noether
  (`gonality_le_of_brillNoether`, `gonality_existence_of_cdpr`).
-/

/-- A graph `G` is **Brill–Noether general** if it has no degree-`d` divisor of rank `≥ r`
  whenever the Brill–Noether number `ρ = g − (r + 1)(g − d + r)` is negative. -/
def BrillNoetherGeneral (G : CFGraph) : Prop :=
  ∀ (r d : ℕ), genus G - (↑r + 1) * (genus G - ↑d + ↑r) < 0 →
    ∀ (D : CFDiv G), deg D = (d : ℤ) → rank G D < (r : ℤ)

/-- **Brill–Noether existence (Baker, Conjecture 3.9(1)) — OPEN.** For every `r, d` with
  Brill–Noether number `ρ = g − (r + 1)(g − d + r) ≥ 0`, there is a degree-`d` divisor of
  rank `≥ r`. Known only for genus `≤ 5`; open even for `r = 1`. -/
def BrillNoetherExistence (G : CFGraph) : Prop :=
  ∀ (r d : ℕ), genus G - (↑r + 1) * (genus G - ↑d + ↑r) ≥ 0 →
    ∃ (D : CFDiv G), rank G D ≥ (r : ℤ) ∧ deg D = (d : ℤ)

/-- On a BN-general graph of genus `g`, the gonality is at least `⌊(g + 3) / 2⌋`.
  This follows because for `r = 1` and `d < ⌊(g+3)/2⌋`, the BN number `ρ < 0`,
  so BN-generality implies no degree-`d` divisor has rank ≥ 1. -/
private lemma gonality_ge_of_bn_general {G : CFGraph} (h_conn : graph_connected G)
    (h_bn_gen : BrillNoetherGeneral G) :
    gonality h_conn ≥ (genus G + 3) / 2 := by
  apply le_csInf ⟨genus G + 1, gonality_leq_genus_add_one h_conn⟩
  intro k ⟨D, hD_rank, hD_deg⟩
  -- D has rank ≥ 1 and deg D = k. Show k ≥ ⌊(g+3)/2⌋.
  -- Contrapositive: if k < ⌊(g+3)/2⌋, BN-generality gives rank < 1.
  by_contra h_lt
  push Not at h_lt
  have hk_pos : k ≥ 1 := one_le_of_gonality_leq ⟨D, hD_rank, hD_deg⟩
  have hk_nat : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (by omega)
  have h_rho_neg : genus G - (↑(1 : ℕ) + 1) * (genus G - ↑k.toNat + ↑(1 : ℕ)) < 0 := by
    simp only [Nat.cast_one]; rw [hk_nat]; omega
  have h_rank_lt := h_bn_gen 1 k.toNat h_rho_neg D (by rw [hD_deg, hk_nat])
  simp only [Nat.cast_one] at h_rank_lt
  linarith

/-- **Brill–Noether general existence:** there exists a Brill–Noether general graph, i.e. a
  connected graph with no degree-`d` divisors of rank `r` whenever
  `ρ = g − (r + 1)(g − d + r) < 0`.

  **Note:** The formal statement as written does not constrain `genus G = g`; the parameter `g`
  is unused. The intended stronger statement (with `genus G = g`) would require constructing a
  Brill–Noether general graph of each genus, as proved by Cools–Draisma–Payne–Robeva.
  The proof here constructs a single-vertex graph (genus 0), which is vacuously BN-general. -/
theorem brill_noether_general_existence (g : ℕ) :
    ∃ (G : CFGraph.{u}) (h_conn : graph_connected G),
      ∀ (r d : ℕ),
        let ρ := genus G - (↑r + 1) * (genus G - ↑d + ↑r)
        ρ < 0 → ∀ (D : CFDiv G), deg D = (d : ℤ) → rank G D < (r : ℤ) := by
  fconstructor;
  use PUnit;
  exact 0;
  all_goals norm_num [ graph_connected ];
  intro r d hD D hD'; rcases r with ( _ | r ) <;> rcases d with ( _ | d ) <;> norm_num [ genus ] at *;
  · linarith;
  · -- Since $D$ is a divisor on a graph with one vertex, it must be the zero divisor.
    have hD_zero : D = 0 := by
      ext v; simp_all +decide [ deg ] ;
    rw [ hD_zero, zero_divisor_rank ] ; norm_num;
  · contrapose! hD';
    exact fun h => by nlinarith [ rank_le_degree ( CFGraph.mk PUnit ( 0 : Multiset ( PUnit × PUnit ) ) ( by simp +decide ) ) D ( r + 1 ) ( by linarith ) ( by
      exact Classical.not_not.1 fun h => hD' |> fun h' => by linarith [ rank_geq_iff ( CFGraph.mk PUnit ( 0 : Multiset ( PUnit × PUnit ) ) ( by simp +decide ) ) D ( r + 1 ) |>.not.mp h ] ; ) ] ;

/-- The genus of a connected graph is non-negative. -/
lemma genus_nonneg {G : CFGraph} (h_conn : graph_connected G) : genus G ≥ 0 := by
  have h1 := gonality_ge_one h_conn
  have h2 := gonality_le_genus_add_one h_conn
  linarith

/-- **Brill–Noether existence, rank `0` case (provable).** Every non-negative degree `d` is the
  degree of an effective divisor, which has rank `≥ 0`. This is the `r = 0` instance of
  `BrillNoetherExistence`. -/
theorem brill_noether_existence_rank_zero {G : CFGraph} (d : ℕ) :
    ∃ (D : CFDiv G), rank G D ≥ (0 : ℤ) ∧ deg D = (d : ℤ) := by
  refine ⟨(d : ℤ) • one_chip (Classical.arbitrary G.V), ?_, ?_⟩
  · have h_eff : effective ((d : ℤ) • one_chip (Classical.arbitrary G.V)) :=
      (Eff G).nsmul_mem (eff_one_chip _) d
    exact (rank_geq_iff G _ 0).mp
      ((rank_nonneg_iff_winnable G _).mpr (winnable_of_effective G _ h_eff))
  · rw [map_zsmul, deg_one_chip, zsmul_one]; simp

/-- **Brill–Noether existence in the non-special / boundary range (provable).** If the
  Brill–Noether number is non-negative *and* `d ≥ g + r − 1`, then a degree-`d` divisor of
  rank `≥ r` exists.

  Two sub-cases, both handled by Riemann–Roch:
  * `d ≥ g + r` (non-special range): the divisor `d • v` already has rank `≥ d − g ≥ r`;
  * `d = g + r − 1` (boundary): take `K − E` with `E` effective of degree `g − r − 1`, so that
    `r(K − E) = r(E) + d − g + 1 ≥ r`.

  This is exactly the part of Baker's existence conjecture that is *unconditionally* true; the
  remaining range `d < g + r − 1` (with `r ≥ 1`) is the open part. -/
theorem brill_noether_existence_of_deg_ge {G : CFGraph} (h_conn : graph_connected G) (r d : ℕ)
    (hρ : genus G - (↑r + 1) * (genus G - ↑d + ↑r) ≥ 0)
    (h_deg : (d : ℤ) ≥ genus G + (r : ℤ) - 1) :
    ∃ (D : CFDiv G), rank G D ≥ (r : ℤ) ∧ deg D = (d : ℤ) := by
  by_cases h : (d : ℤ) ≥ genus G + (r : ℤ)
  · -- Non-special range d ≥ g + r: `D = d • v` has rank ≥ deg D − g = d − g ≥ r.
    let v := Classical.arbitrary G.V
    refine ⟨(d : ℤ) • one_chip v, ?_, ?_⟩
    · have h_rr := riemann_roch_for_graphs h_conn ((d : ℤ) • one_chip v)
      have h_neg := rank_geq_neg_one G (canonical_divisor G - (d : ℤ) • one_chip v)
      have h_deg' : deg ((d : ℤ) • one_chip v) = (d : ℤ) := by
        rw [map_zsmul, deg_one_chip, zsmul_one]; simp
      linarith
    · rw [map_zsmul, deg_one_chip, zsmul_one]; simp
  · -- Boundary: `g + r − 1 ≤ d < g + r` forces `d = g + r − 1`; use `D = K − E` (Serre duality).
    have hd_eq : (d : ℤ) = genus G + (r : ℤ) - 1 := by omega
    have hgdr : genus G - (d : ℤ) + (r : ℤ) = 1 := by rw [hd_eq]; ring
    have h_nonneg : (0 : ℤ) ≤ genus G - (r : ℤ) - 1 := by
      have h' := hρ; rw [hgdr, mul_one] at h'; linarith
    let E := ((genus G - (r : ℤ) - 1).toNat : ℤ) • one_chip (Classical.arbitrary G.V)
    have h_E_deg : deg E = genus G - (r : ℤ) - 1 := by
      show deg (((genus G - (r : ℤ) - 1).toNat : ℤ) • one_chip (Classical.arbitrary G.V)) = _
      rw [map_zsmul, deg_one_chip, zsmul_one,
        show ((genus G - (r : ℤ) - 1).toNat : ℤ) = genus G - (r : ℤ) - 1 from
          Int.toNat_of_nonneg h_nonneg]
      simp
    have h_E_eff : effective E := (Eff G).nsmul_mem (eff_one_chip _) _
    refine ⟨canonical_divisor G - E, ?_, ?_⟩
    · have h_rr := riemann_roch_for_graphs h_conn (canonical_divisor G - E)
      have h_KD : canonical_divisor G - (canonical_divisor G - E) = E := by simp
      rw [h_KD] at h_rr
      have h_rE_ge : rank G E ≥ 0 :=
        (rank_geq_iff G E 0).mp
          ((rank_nonneg_iff_winnable G E).mpr (winnable_of_effective G E h_E_eff))
      have h_deg_D : deg (canonical_divisor G - E) = (d : ℤ) := by
        rw [deg.map_sub, degree_of_canonical_divisor, h_E_deg, hd_eq]; ring
      linarith
    · rw [deg.map_sub, degree_of_canonical_divisor, h_E_deg, hd_eq]; ring

/-- **Gonality conjecture (Baker, Conjecture 3.10(1)) — OPEN.** Every connected graph satisfies
  `gon(G) ≤ ⌊(g + 3) / 2⌋`. This is exactly the `r = 1` case of `BrillNoetherExistence`. -/
def GonalityConjecture {G : CFGraph} (h_conn : graph_connected G) : Prop :=
  gonality h_conn ≤ (genus G + 3) / 2

/-- The gonality conjecture is implied by Brill–Noether existence: apply it with `r = 1` and
  `d = ⌊(g + 3) / 2⌋`, where the Brill–Noether number `ρ = 2d − g − 2 ≥ 0`, to obtain a
  degree-`d` divisor of rank `≥ 1`. -/
theorem gonality_le_of_brillNoether {G : CFGraph} (h_conn : graph_connected G)
    (h_bn : BrillNoetherExistence G) : GonalityConjecture h_conn := by
  show gonality h_conn ≤ (genus G + 3) / 2
  set d_nat : ℕ := ((genus G + 3) / 2).toNat with d_nat_def
  have h_gnn := genus_nonneg h_conn
  have h_ge : (genus G + 3) / 2 ≥ 0 := by omega
  have h_cast : (d_nat : ℤ) = (genus G + 3) / 2 := Int.toNat_of_nonneg h_ge
  have h_rho : genus G - (↑(1 : ℕ) + 1) * (genus G - ↑d_nat + ↑(1 : ℕ)) ≥ 0 := by
    simp only [Nat.cast_one]; rw [h_cast]; ring_nf; omega
  obtain ⟨D, hD_rank, hD_deg⟩ := h_bn 1 d_nat h_rho
  have h_gonality_leq : gonality_leq G (d_nat : ℤ) := ⟨D, hD_rank, hD_deg⟩
  have h_bdd : BddBelow {k : ℤ | gonality_leq G k} := ⟨1, fun k hk => one_le_of_gonality_leq hk⟩
  have h_le : gonality h_conn ≤ (d_nat : ℤ) := csInf_le h_bdd h_gonality_leq
  linarith

/-- A graph is a **Brill–Noether general graph** if it satisfies both halves of Brill–Noether
  theory: existence (`ρ ≥ 0 ⇒ a divisor of the predicted degree and rank exists`) and generality
  (`ρ < 0 ⇒ no such divisor exists`). -/
def BrillNoetherGeneralGraph (G : CFGraph) : Prop :=
  BrillNoetherExistence G ∧ BrillNoetherGeneral G

/-- **Cools–Draisma–Payne–Robeva existence — not yet formalized.** Every genus contains a
  connected Brill–Noether general graph. The only known proof uses tropical chains of loops with
  generic edge lengths; that metric-graph machinery is not in Mathlib, so we expose this as a
  hypothesis rather than asserting it. -/
def BrillNoetherGeneralGraphExists (g : ℕ) : Prop :=
  ∃ (G : CFGraph.{u}) (_ : graph_connected G),
    genus G = (g : ℤ) ∧ BrillNoetherGeneralGraph G

/-- **Gonality conjecture, existence version (Baker, Conjecture 3.10(2)).** Conditional on the
  Cools–Draisma–Payne–Robeva existence of a Brill–Noether general graph in genus `g`, there is a
  connected graph of genus `g` with gonality exactly `⌊(g + 3) / 2⌋`. The upper bound is supplied
  by `gonality_le_of_brillNoether` and the lower bound by `gonality_ge_of_bn_general`. -/
theorem gonality_existence_of_cdpr (g : ℕ) (h : BrillNoetherGeneralGraphExists.{u} g) :
    ∃ (G : CFGraph.{u}) (h_conn : graph_connected G),
      genus G = (g : ℤ) ∧ gonality h_conn = ((g : ℤ) + 3) / 2 := by
  obtain ⟨G, h_conn, h_genus, h_bn_exist, h_bn_gen⟩ := h
  have hle : gonality h_conn ≤ (genus G + 3) / 2 := gonality_le_of_brillNoether h_conn h_bn_exist
  have hge : gonality h_conn ≥ (genus G + 3) / 2 := gonality_ge_of_bn_general h_conn h_bn_gen
  exact ⟨G, h_conn, h_genus, le_antisymm (h_genus ▸ hle) (h_genus ▸ hge)⟩
