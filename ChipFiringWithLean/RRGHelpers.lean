import ChipFiringWithLean.Orientation
import ChipFiringWithLean.Rank
-- import Paperproof

set_option linter.unusedVariables false
set_option trace.split.failure true

open Multiset Finset

/-!
## Maximal superstable configurations and maximal unwinnable divisors

This section establishes the correspondence between maximal superstable configurations and
maximal unwinnable divisors:

- A superstable configuration $c$ is maximal if and only if $\deg(c) = g$
  (`maximal_superstable_config_prop`).
- A divisor $D$ is maximal unwinnable if and only if its canonical $q$-reduced representative
  is `qReducedConfig h_conn q D - q`, with `qReducedConfig h_conn q D` maximal superstable
  (`maximal_unwinnable_char`).
- Every maximal unwinnable divisor has degree $g - 1$ (`maximal_unwinnable_deg`).
-/

/-- The chosen unique `q`-reduced representative of the linear equivalence class of `D`. -/
noncomputable def qReducedRep {G : CFGraph}
    (h_conn : graph_connected G) (q : G.V) (D : CFDiv G) : CFDiv G :=
  Classical.choose (unique_q_reduced h_conn q D)

/-- The canonical representative is linearly equivalent to `D` and `q`-reduced. -/
lemma qReducedRep_spec {G : CFGraph}
    (h_conn : graph_connected G) (q : G.V) (D : CFDiv G) :
    linear_equiv G D (qReducedRep h_conn q D) ∧ q_reduced G q (qReducedRep h_conn q D) :=
  (Classical.choose_spec (unique_q_reduced h_conn q D)).1

/-- The configuration obtained from the canonical `q`-reduced representative of `D`
by zeroing out the chips at `q`. -/
noncomputable def qReducedConfig {G : CFGraph}
    (h_conn : graph_connected G) (q : G.V) (D : CFDiv G) : Config G q :=
  toConfig ⟨qReducedRep h_conn q D, (qReducedRep_spec h_conn q D).2.1⟩

/-- The canonical configuration attached to `D` is superstable. -/
lemma qReducedConfig_superstable {G : CFGraph}
    (h_conn : graph_connected G) (q : G.V) (D : CFDiv G) :
    superstable G q (qReducedConfig h_conn q D) := by
  exact q_reduced_toConfig_superstable G q (qReducedRep h_conn q D) (qReducedRep_spec h_conn q D).2

/-- Every divisor $D$ is linearly equivalent to `qReducedConfig h_conn q D + k·q`
for some integer `k`; in particular, it is linearly equivalent to `c + k·q` for a
superstable configuration `c`. -/
lemma superstable_of_divisor {G : CFGraph} (h_conn : graph_connected G) (q : G.V) (D : CFDiv G) :
  ∃ (c : Config G q) (k : ℤ),
    linear_equiv G D (c.vertex_degree + k • (one_chip q)) ∧
    superstable G q c := by
  let D' := qReducedRep h_conn q D
  let c := qReducedConfig h_conn q D
  use c, D' q
  constructor
  ·
    have h := (qReducedRep_spec h_conn q D).1
    rw [q_reduced_eq_vertex_degree_add_q G q (qReducedRep h_conn q D) (qReducedRep_spec h_conn q D).2] at h
    simpa [D', c] using h
  ·
    simpa [c] using qReducedConfig_superstable h_conn q D

/-- If $D$ is unwinnable and $D \sim c + k \cdot q$ for a superstable $c$, then $k < 0$. -/
lemma superstable_of_divisor_negative_k (G : CFGraph) (q : G.V) (D : CFDiv G) :
  ¬(winnable G D) →
  ∀ (c : Config G q) (k : ℤ),
    linear_equiv G D (c.vertex_degree + k • (one_chip q)) →
    superstable G q c →
    k < 0 := by
  intro h_not_winnable c k h_equiv h_super
  contrapose! h_not_winnable with k_nonneg
  let D' := c.vertex_degree + k • (one_chip q)
  have D'_eff : effective D' := by
    rw [show D' = toDiv (config_degree c + k) c by
      dsimp [D']
      rw [toDiv_config_degree_add]]
    exact (config_eff (config_degree c + k) c).2 (by linarith)
  have h_winnable_D' : winnable G D' := winnable_of_effective G D' D'_eff
  apply winnable_equiv_winnable G D' D h_winnable_D'
  apply (linear_equiv_is_equivalence G).symm h_equiv


/-- If $D$ is maximal unwinnable and $q$-reduced, then $D(q) = -1$. -/
lemma maximal_unwinnable_q_reduced_chips_at_q (G : CFGraph) (q : G.V) (D : CFDiv G) :
  maximal_unwinnable G D → q_reduced G q D → D q = -1 := by
  intro h_max_unwin h_qred
  have h_neg : D q < 0 := by
    contrapose! h_max_unwin
    unfold maximal_unwinnable
    push Not
    intro h_unwin
    absurd h_unwin
    suffices effective D by
      exact winnable_of_effective G D this
    intro v
    by_cases hv : v = q
    · rw [hv]
      exact h_max_unwin
    · exact h_qred.1 v (by simp [hv])
  have h_add_win : winnable G (D + one_chip q) := by exact (h_max_unwin.2 q)
  have h_eff : effective (D + one_chip q) := by
    apply effective_of_winnable_and_q_reduced G q (D + one_chip q) h_add_win
    -- Prove q-reducedness of D + one_chip q
    constructor
    · intro v hv
      have h_v_ne_q : v ≠ q := by
        exact Set.mem_setOf.mp hv
      rw [add_apply]
      simp [h_v_ne_q]
      apply h_qred.1 v hv
    · intro S hS_subset hS_nonempty
      -- Use the q_reducedness of D
      have := h_qred.2
      specialize this S hS_subset hS_nonempty
      rcases this with ⟨v, hv_in_S, h_dv_lt_outdeg⟩
      use v
      simp [hv_in_S]
      suffices one_chip q v = 0 by
        rw [this]
        simp [h_dv_lt_outdeg]
      suffices q ≠ v by
        rw [one_chip_apply_other]
        exact this
      intro h_absurd
      rw [← h_absurd] at hv_in_S
      apply hS_subset at hv_in_S
      simp at hv_in_S
  have h_nonneg : D q + 1 ≥ 0 := by
    have h := h_eff q
    rw [add_apply] at h
    simp at h
    exact h
  linarith

/-- A maximal superstable configuration has degree equal to the genus.
This is [Corry-Perkinson], Corollary 4.9(1), "only if" direction. -/
lemma degree_max_superstable {G : CFGraph} {q : G.V} (c : Config G q) (h_max : maximal_superstable G c): config_degree c = genus G := by
  have := maximal_superstable_orientation G q c h_max
  rcases this with ⟨O, hO, h_orient_eq⟩
  rw [← h_orient_eq]
  exact config_degree_from_O O hO

/-- If `D` is maximal unwinnable and `q`-reduced, then any configuration `c` satisfying
`D = toDiv (deg D) c` must realize `D` as `c - q`. This is the `q`-reduced core of
[Corry-Perkinson], Corollary 4.9(2), "only if" direction. -/
lemma maximal_unwinnable_q_reduced_form (G : CFGraph) (q : G.V) (D : CFDiv G) (c : Config G q) :
  maximal_unwinnable G D → q_reduced G q D → D = toDiv (deg D) c → D = c.vertex_degree - one_chip q := by
  intro h_max_unwinnable h_qred h_toDeg
  have h_c_eq : c = toConfig ⟨D, h_qred.1⟩ := by
    apply (eq_config_iff_eq_div (deg D) c (toConfig ⟨D, h_qred.1⟩)).mpr
    exact h_toDeg.symm.trans (q_reduced_toDiv_toConfig G q D h_qred).symm
  calc
    D = (toConfig ⟨D, h_qred.1⟩).vertex_degree - one_chip q := by
      exact q_reduced_eq_vertex_degree_sub_one_chip G q D h_qred
        (maximal_unwinnable_q_reduced_chips_at_q G q D h_max_unwinnable h_qred)
    _ = c.vertex_degree - one_chip q := by rw [h_c_eq]

/-- Lemma: Superstable configuration degree is bounded by genus -/
lemma helper_superstable_degree_bound (G : CFGraph) (q : G.V) (c : Config G q) :
  superstable G q c → config_degree c ≤ genus G := by
  intro h_super
  have := maximal_superstable_exists G q c h_super
  rcases this with ⟨c_max, h_maximal, h_ge_c⟩
  have h_genus_eq := degree_max_superstable c_max h_maximal
  rw [← h_genus_eq]
  dsimp [config_degree]
  dsimp [deg]
  apply Finset.sum_le_sum
  intro v hv
  specialize h_ge_c v
  exact h_ge_c

/-- Lemma: If a superstable configuration has degree equal to g, it is maximal
[Corry-Perkinson], Corollary 4.9(1), "if" direction. -/
lemma helper_degree_g_implies_maximal (G : CFGraph) (q : G.V) (c : Config G q) :
  superstable G q c → config_degree c = genus G → maximal_superstable G c := by
  intro h_super h_deg_eq
  -- Choose a maximal above c (we'll show it's equal to c)
  have := maximal_superstable_exists G q c h_super
  rcases this with ⟨c_max, h_maximal, h_ge_c⟩
  have c_max_deg : config_degree c_max = genus G := by
    exact degree_max_superstable c_max h_maximal
  let E := c_max.vertex_degree - c.vertex_degree
  have E_eff : E ≥ 0 := by
    intro v
    specialize h_ge_c v
    dsimp [E]
    linarith
  have E_deg : deg E = 0 := by
    dsimp [E]
    rw [map_sub]
    dsimp [config_degree] at h_deg_eq c_max_deg
    rw [h_deg_eq, c_max_deg]
    simp
  have E_0 : E = 0 := eff_degree_zero E E_eff E_deg
  dsimp [E] at E_0
  have : c_max.vertex_degree = c.vertex_degree := by
    rw [← sub_eq_zero, E_0]
  have : c_max = c := (eq_config_iff_eq_vertex_degree c_max c).mpr this
  rw [← this]
  exact h_maximal

/-- A superstable configuration is maximal if and only if its degree equals the genus.
This is [Corry-Perkinson], Corollary 4.9(1). -/
theorem maximal_superstable_config_prop (G : CFGraph) (q : G.V) (c : Config G q) :
  superstable G q c → (maximal_superstable G c ↔ config_degree c = genus G) := by
  intro h_super
  constructor
  { -- Forward direction: maximal_superstable → degree = g
    intro h_max
    exact degree_max_superstable c h_max
  }
  { -- Reverse direction: degree = g → maximal_superstable
    intro h_deg
    -- Apply the lemma that degree g implies maximality
    exact helper_degree_g_implies_maximal G q c h_super h_deg }


/-- A divisor of degree at least $g$ is winnable. -/
lemma winnable_of_deg_ge_genus {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) : deg D ≥ genus G → winnable G D := by
  intro h_deg_ge_g
  let q := Classical.arbitrary G.V
  rcases (exists_q_reduced_representative h_conn q D) with ⟨D_qred, h_equiv, h_qred⟩
  have := (q_reduced_superstable_correspondence G q D_qred).mp h_qred
  rcases this with ⟨c, h_super, h_D_eq⟩
  have := maximal_superstable_exists G q c h_super
  rcases this with ⟨c_max, h_maximal, h_ge_c⟩
  have h_deg_c : config_degree c ≤ genus G := by
    have := degree_max_superstable c_max h_maximal
    rw [← this]
    apply Finset.sum_le_sum
    intro v hv
    specialize h_ge_c v
    exact h_ge_c
  have h_ineq := le_trans h_deg_c h_deg_ge_g
  have D_deg : deg D = deg D_qred := linear_equiv_preserves_deg G D D_qred h_equiv
  rw [D_deg] at h_ineq
  have c_from_D : c = toConfig ⟨D_qred, h_qred.1⟩ := by
    rw [eq_config_iff_eq_vertex_degree]
    funext v
    dsimp [toConfig]
    dsimp [toDiv] at h_D_eq
    rw [h_D_eq]
    simp
    by_cases hvq : v = q
    · rw [hvq]
      simp [c.q_zero]
    · simp [hvq]
  have deg_eq := config_degree_div_degree ⟨D_qred, h_qred.1⟩
  simp at deg_eq
  rw [← c_from_D] at deg_eq
  rw [← D_deg] at deg_eq
  have eff_q : D_qred q ≥ 0 := by
    linarith [h_deg_ge_g, h_deg_c]
  use D_qred
  constructor
  · -- Prove D_qred is effective
    intro v
    by_cases hvq : v = q
    · rw [hvq]
      exact eff_q
    · -- v ≠ q
      rw [h_D_eq]
      dsimp [toDiv]
      simp
      rw [one_chip_apply_other q v]
      simp [c.non_negative v]
      intro h; rw [h] at hvq; contradiction
  · -- Prove linear equivalence
    exact h_equiv

/-- Lemma: Adding a chip anywhere to c'-q makes it winnable when c' is maximal superstable -/
lemma helper_maximal_superstable_chip_winnable_exact {G : CFGraph} (h_conn : graph_connected G) (q : G.V) (c' : Config G q) :
  maximal_superstable G c' →
  ∀ (v : G.V), winnable G (c'.vertex_degree- (one_chip q) + (one_chip v)) := by
  intro h_max_superstable v
  let D' := c'.vertex_degree - one_chip q + one_chip v
  have deg_ineq : deg D' ≥ genus G := by
    calc
      deg D' = config_degree c' := by
        dsimp [D']
        simp [config_degree]
      _ = genus G := degree_max_superstable c' h_max_superstable
      _ ≥ genus G := by rfl
  exact winnable_of_deg_ge_genus h_conn D' deg_ineq

/-- A maximal unwinnable `q`-reduced divisor is the canonical `toConfig` form minus one chip at `q`. -/
lemma maximal_unwinnable_q_reduced_toConfig_form {G : CFGraph} (q : G.V) (D : CFDiv G)
    (h_max : maximal_unwinnable G D) (h_qred : q_reduced G q D) :
    D = (toConfig ⟨D, h_qred.1⟩).vertex_degree - one_chip q := by
  exact q_reduced_eq_vertex_degree_sub_one_chip G q D h_qred
    (maximal_unwinnable_q_reduced_chips_at_q G q D h_max h_qred)

/-- A divisor of the form `c - q` is maximal unwinnable when `c` is maximal superstable. -/
lemma maximal_unwinnable_of_maximal_superstable_form {G : CFGraph}
    (h_conn : graph_connected G) (q : G.V) (c : Config G q) :
    maximal_superstable G c → maximal_unwinnable G (c.vertex_degree - one_chip q) := by
  intro h_max_c
  refine ⟨helper_superstable_to_unwinnable h_conn q c h_max_c, ?_⟩
  intro v
  exact helper_maximal_superstable_chip_winnable_exact h_conn q c h_max_c v

/-- For a `q`-reduced divisor, maximal unwinnability is equivalent to the maximal
superstability of its canonical configuration together with the canonical `c - q` form. -/
lemma maximal_unwinnable_q_reduced_toConfig_iff {G : CFGraph}
    (h_conn : graph_connected G) (q : G.V) (D : CFDiv G) (h_qred : q_reduced G q D) :
    maximal_unwinnable G D ↔
    maximal_superstable G (toConfig ⟨D, h_qred.1⟩) ∧
    D = (toConfig ⟨D, h_qred.1⟩).vertex_degree - one_chip q := by
  constructor
  · intro h_max
    constructor
    · let c : Config G q := toConfig ⟨D, h_qred.1⟩
      have h_super_c : superstable G q c := q_reduced_toConfig_superstable G q D h_qred
      have h_form_D : D = c.vertex_degree - one_chip q := by
        exact maximal_unwinnable_q_reduced_toConfig_form q D h_max h_qred
      by_contra h_not_max_c
      rcases maximal_superstable_exists G q c h_super_c with ⟨c', h_max_c', h_ge⟩
      have h_ne : c' ≠ c := by
        intro h_eq
        apply h_not_max_c
        simpa [h_eq] using h_max_c'
      have h_strict : ∃ v : G.V, c.vertex_degree v + 1 ≤ c'.vertex_degree v := by
        by_contra h_no
        push Not at h_no
        have h_c'_le_c : c' ≤ c := by
          intro v
          linarith [h_no v]
        exact h_ne ((le_antisymm h_ge h_c'_le_c).symm)
      rcases h_strict with ⟨v, h_v_strict⟩
      have h_H_eff : effective (c'.vertex_degree - c.vertex_degree - one_chip v) := by
        intro w
        by_cases h_wv : w = v
        · rw [h_wv]
          simp [one_chip]
          linarith [h_ge v, h_v_strict]
        · simp [one_chip, h_wv]
          linarith [h_ge w]
      have h_D''_eq :
          c'.vertex_degree - one_chip q =
            (c'.vertex_degree - c.vertex_degree - one_chip v) + (D + one_chip v) := by
        rw [h_form_D]
        funext w
        simp [sub_eq_add_neg]
        abel_nf
      have h_D''_unwin : ¬winnable G (c'.vertex_degree - one_chip q) :=
        helper_superstable_to_unwinnable h_conn q c' h_max_c'
      apply h_D''_unwin
      rw [h_D''_eq]
      exact winnable_add_winnable G (c'.vertex_degree - c.vertex_degree - one_chip v) (D + one_chip v)
        (winnable_of_effective G _ h_H_eff) (h_max.2 v)
    · exact maximal_unwinnable_q_reduced_toConfig_form q D h_max h_qred
  · rintro ⟨h_max_c, h_form⟩
    rw [h_form]
    exact maximal_unwinnable_of_maximal_superstable_form h_conn q _ h_max_c


/-- A divisor $D$ is maximal unwinnable if and only if its canonical `q`-reduced representative
is `qReducedConfig h_conn q D - q`, with `qReducedConfig h_conn q D` maximal superstable.
This is [Corry-Perkinson], Corollary 4.9(2), in canonical form. -/
theorem maximal_unwinnable_char {G : CFGraph} (h_conn : graph_connected G) (q : G.V) (D : CFDiv G) :
  maximal_unwinnable G D ↔
    maximal_superstable G (qReducedConfig h_conn q D) ∧
    qReducedRep h_conn q D =
      (qReducedConfig h_conn q D).vertex_degree - one_chip q := by
  let D' := qReducedRep h_conn q D
  have h_qred_D' : q_reduced G q D' := (qReducedRep_spec h_conn q D).2
  have h_core := maximal_unwinnable_q_reduced_toConfig_iff h_conn q D' h_qred_D'
  constructor
  · intro h_max_unwinnable_D
    have h_max_D' : maximal_unwinnable G D' :=
      maximal_unwinnable_preserved G D D' h_max_unwinnable_D (qReducedRep_spec h_conn q D).1
    simpa [D', qReducedConfig] using h_core.mp h_max_D'
  · intro h_can
    have h_max_D' : maximal_unwinnable G D' := by
      simpa [D', qReducedConfig] using h_core.mpr h_can
    exact maximal_unwinnable_preserved G D' D h_max_D'
      ((linear_equiv_is_equivalence G).symm (qReducedRep_spec h_conn q D).1)

/-- Combined characterization: the degree criterion for maximal superstable configurations
and the canonical characterization of maximal unwinnable divisors, packaged together. -/
theorem superstable_and_maximal_unwinnable {G : CFGraph} (h_conn : graph_connected G) (q : G.V)
    (c : Config G q) (D : CFDiv G) :
    (superstable G q c →
     (maximal_superstable G c ↔ config_degree c = genus G)) ∧
    (maximal_unwinnable G D ↔
      maximal_superstable G (qReducedConfig h_conn q D) ∧
      qReducedRep h_conn q D =
        (qReducedConfig h_conn q D).vertex_degree - one_chip q) := by
  exact ⟨maximal_superstable_config_prop G q c,
         maximal_unwinnable_char h_conn q D⟩

/-- A maximal unwinnable divisor has degree $g - 1$, computed from its canonical
`q`-reduced representative and canonical configuration.
This is [Corry-Perkinson], Corollary 4.9(4). -/
theorem maximal_unwinnable_deg
  {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) :
  maximal_unwinnable G D → deg D = genus G - 1 := by
  intro h_max_unwin

  let q := Classical.arbitrary G.V

  have h_char := maximal_unwinnable_char h_conn q D
  have h_max_cfg : maximal_superstable G (qReducedConfig h_conn q D) := (h_char.mp h_max_unwin).1
  have h_rep_form :
      qReducedRep h_conn q D =
        (qReducedConfig h_conn q D).vertex_degree - one_chip q := (h_char.mp h_max_unwin).2
  have h_deg_D' : deg (qReducedRep h_conn q D) = genus G - 1 := calc
    deg (qReducedRep h_conn q D) =
        deg ((qReducedConfig h_conn q D).vertex_degree - one_chip q) := by rw [h_rep_form]
    _ = config_degree (qReducedConfig h_conn q D) - 1 :=
        deg_vertex_degree_sub_one_chip (c := qReducedConfig h_conn q D)
    _ = genus G - 1 := by rw [degree_max_superstable (qReducedConfig h_conn q D) h_max_cfg]
  have h_deg_eq : deg D = deg (qReducedRep h_conn q D) :=
    linear_equiv_preserves_deg G D (qReducedRep h_conn q D) (qReducedRep_spec h_conn q D).1
  rw [h_deg_eq, h_deg_D']

/-- The map sending an acyclic orientation with source $q$ to its orientation divisor is
injective, and every maximal unwinnable divisor has degree $g - 1$.
The injectivity claim is [Corry-Perkinson], Corollary 4.9(3). -/
theorem acyclic_orientation_maximal_unwinnable_correspondence_and_degree
    {G : CFGraph} (h_conn : graph_connected G) (q : G.V) :
    (Function.Injective (λ (O : {O : CFOrientation G // is_acyclic G O ∧ is_source G O q}) =>
      λ v => (indeg G O.val v) - if v = q then 1 else 0)) ∧
    (∀ D : CFDiv G, maximal_unwinnable G D → deg D = genus G - 1) := by
  constructor
  { -- Part 1: Injection proof
    intros O₁ O₂ h_eq
    have h_indeg : ∀ v : G.V, indeg G O₁.val v = indeg G O₂.val v := by
      intro v
      have := congr_fun h_eq v
      by_cases hv : v = q
      · have h₁ := O₁.prop.2; have h₂ := O₂.prop.2
        dsimp [is_source] at h₁ h₂
        rw [hv, h₁, h₂]
      · simp [hv] at this
        exact this
    exact Subtype.ext (orientation_determined_by_indegrees O₁.val O₂.val O₁.prop.1 O₂.prop.1 h_indeg)
  }
  { -- Part 2: Degree characterization
    -- This now correctly refers to the theorem defined above
    intro D hD
    exact maximal_unwinnable_deg h_conn D hD
  }






/-!
## The main Riemann-Roch inequality

`rank_degree_inequality` establishes the strict inequality
$$\deg(D) - g < r(D) - r(K_G - D),$$
which is the main step toward the Riemann-Roch theorem for graphs. The proof uses
Dhar's burning algorithm to find a maximal superstable configuration dominating the
configuration associated to $D - E$, then dualizes via the reverse orientation to
bound $r(K_G - D)$.
-/

/-- The strict Riemann-Roch inequality: $\deg(D) - g < r(D) - r(K_G - D)$. -/
theorem rank_degree_inequality
    {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) :
    deg D - genus G < rank G D - rank G (canonical_divisor G - D) := by
  -- Get rank value for D
  let r := rank G D

  -- Get effective divisor E using rank characterization
  rcases rank_get_effective G D with ⟨E, h_E_eff, h_E_deg, h_D_E_unwin⟩

  -- Fix a vertex q
  let q := Classical.arbitrary G.V

  -- Apply Dhar's algorithm to D - E to get q-reduced form
  rcases superstable_of_divisor h_conn q (D - E) with ⟨c, k, h_equiv, h_super⟩

  have h_k_neg := superstable_of_divisor_negative_k G q (D - E) h_D_E_unwin c k h_equiv h_super

  -- Get maximal superstable c' ≥ c
  rcases maximal_superstable_exists G q c h_super with ⟨c', h_max', h_ge⟩

  -- Let O be corresponding acyclic orientation using the bijection
  rcases orientation_superstable_bijection G q with ⟨_, h_surj⟩
  -- Apply h_surj to the subtype element ⟨c', h_max'⟩
  rcases h_surj ⟨c', h_max'⟩ with ⟨O_subtype, h_eq_c'⟩ -- O_subtype is {O // acyclic_with_unique_source}
  let O := O_subtype.val
  let hO := O_subtype.prop
  let O_acyc := hO.1
  let O_unique_source := hO.2

  -- Get configuration c' from orientation O_subtype
  let c'_config := orientation_to_config G O q hO

  -- Check consistency: h_eq_c' implies c'_config = c'
  have h_orient_eq_c' : c'_config = c' := by exact Subtype.mk.inj h_eq_c'

  -- Check consistency (assuming h_eq_c' implies c' = c'_config)
  -- Define H := (c' - c) - (k + 1)q as a divisor (using original c')
  let H : CFDiv G := -(k+1) • (one_chip q) + c'.vertex_degree - c.vertex_degree

  have h_H_eff : effective H := by
    have : c.vertex_degree ≤ c'.vertex_degree := h_ge
    have diff_eff : effective (c'.vertex_degree - c.vertex_degree) := by
      rw [sub_eff_iff_geq]
      exact this
    have src_eff : effective (-(k+1) • one_chip q)  := by
      intro v
      rw [smul_apply]
      apply mul_nonneg
      · -- Prove -(k + 1) ≥ 0
        linarith [h_k_neg]
      · -- Prove one_chip q v ≥ 0
        exact eff_one_chip q v
    -- Sum of two effective divisors is effective
    have := (Eff G).add_mem src_eff diff_eff
    rw [← add_sub_assoc] at this
    exact this

  -- The following divisor is called a "moderator" in the literature.
  -- It is a maximal unwinnable divisor ≥ D-E, as we will show.
  let M := c'.vertex_degree - one_chip q
  have M_eq : linear_equiv G M (D - E + H) := by
    dsimp[M,H]
    dsimp [linear_equiv]
    dsimp [linear_equiv] at h_equiv
    rw [principal_iff_eq_prin] at h_equiv
    rcases h_equiv with ⟨σ, eq_σ⟩
    rw [principal_iff_eq_prin]
    use (-σ)
    rw [map_neg]
    rw [← eq_σ]
    funext v; simp; ring

  have h_M_O : M = ordiv G O := by
    have c'_eq : c' = toConfig (orqed O hO) := by
      rw [← h_orient_eq_c']
      dsimp [c'_config]
      rw [config_and_divisor_from_O O hO]

    have : toDiv (genus G - 1) (toConfig (orqed O hO)) = ordiv G O := by
      calc
        toDiv (genus G - 1) (toConfig (orqed O hO))
            = toDiv (deg (orqed O hO).D) (toConfig (orqed O hO)) := by
                have h_deg_orqed : deg (orqed O hO).D = genus G - 1 := by
                  simpa [orqed] using degree_ordiv O
                rw [h_deg_orqed]
        _ = (orqed O hO).D := div_of_config_of_div (orqed O hO)
        _ = ordiv G O := rfl
    rw [← this]
    dsimp [M,toDiv]
    rw [c'_eq]
    have : (genus G - 1 - config_degree (toConfig (orqed O hO))) = -1 := by
      have h_cfg_deg : config_degree (toConfig (orqed O hO)) = genus G := by
        rw [← config_and_divisor_from_O O hO]
        exact config_degree_from_O O hO
      rw [h_cfg_deg]
      ring
    simp [this]
    rw [sub_eq_add_neg]

  -- Complete h_DO_unwin
  have h_DO_unwin : maximal_unwinnable G M := by
    constructor
    · -- First show it's unwinnable
      exact helper_superstable_to_unwinnable h_conn q c' h_max'

    · -- Then show adding a chip anywhere makes it winnable
      exact helper_maximal_superstable_chip_winnable_exact h_conn q c' h_max'

  -- Now dualize, to get a statement about the reverse orientation
  let O' := O.reverse
  have O'_acyc : is_acyclic G O' := is_acyclic_reverse_of_is_acyclic G O O_acyc

  let M' := ordiv G O'
  let D' := canonical_divisor G - D
  have M'_eq : M' = canonical_divisor G - M := by
    rw [← divisor_reverse_orientation O]
    rw [h_M_O]
    abel

  have h_M'_unwin : ¬ (winnable G M') :=
    ordiv_unwinnable G O' O'_acyc
  have h_M'_equiv : linear_equiv G (D' - H + E) M' := by
    rw [M'_eq]
    dsimp [D', linear_equiv]
    dsimp [linear_equiv] at M_eq
    rw [principal_iff_eq_prin] at M_eq
    rw [principal_iff_eq_prin]
    rcases M_eq with ⟨σ, eq_σ⟩
    use σ
    rw [← eq_σ]
    abel
  have h_D'_H : ¬ winnable G (D' - H) := by
    contrapose! h_M'_unwin
    have := winnable_add_winnable G (D' - H) E h_M'_unwin (winnable_of_effective G E h_E_eff)
    apply winnable_equiv_winnable G (D'-H+E) M' this h_M'_equiv

  have ineq : deg H > rank G D' := by
    contrapose! h_D'_H
    apply (rank_geq_iff G D' (deg H)).mpr at h_D'_H
    dsimp [rank_geq] at h_D'_H
    specialize h_D'_H H ⟨h_H_eff, rfl⟩
    exact h_D'_H

  -- Finally, degree calculations to finish the inequality
  dsimp [D'] at ineq
  have : deg H = - deg D + deg E + deg M := by
    rw [linear_equiv_preserves_deg G M (D - E + H) M_eq]
    simp
    linarith
  rw [this] at ineq
  have := degree_ordiv O
  rw [← h_M_O] at this
  linarith
