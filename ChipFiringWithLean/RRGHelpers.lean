import ChipFiringWithLean.Orientation
import ChipFiringWithLean.Rank
import Paperproof

set_option linter.unusedVariables false
set_option trace.split.failure true

open Multiset Finset

-- Assume V is a finite type with decidable equality
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]

/-
## Maximal superstable configurations, maximal unwinnable divisors, and the correspondences between them
-/

/-- Given any divisor D, there exists a superstable configuration c and an integer k such that
    D is linearly equivalent to c + k * δ_q.
    Proven using `exists_q_reduced_representative` and `q_reduced_superstable_correspondence`.
-/
lemma superstable_of_divisor {G : CFGraph V} (h_conn : graph_connected G) (q : V) (D : CFDiv V) :
  ∃ (c : Config V q) (k : ℤ),
    linear_equiv G D (c.vertex_degree + k • (one_chip q)) ∧
    superstable G q c := by
  -- 1. Get the q-reduced representative D' for D using the lemma
  rcases exists_q_reduced_representative h_conn q D with ⟨D', h_equiv_D_D', h_qred_D'⟩

  -- 2. Use the correspondence lemma to get c from D'
  rcases (q_reduced_superstable_correspondence G q D').mp h_qred_D' with ⟨c, h_super_c, h_D'_eq_c_minus_delta_q⟩


  unfold toDiv at h_D'_eq_c_minus_delta_q
  let k := deg D' - config_degree c
  use c
  use k
  constructor
  · -- Prove linear equivalence: linear_equiv G D (λ v => c
    have h := h_equiv_D_D'
    rw [h_D'_eq_c_minus_delta_q] at h
    exact h
  · -- Prove superstable G q c
    exact h_super_c

/--
A superstable configuration associated to an unwinnable divisor has negative degree at q.
-/
lemma superstable_of_divisor_negative_k (G : CFGraph V) (q : V) (D : CFDiv V) :
  ¬(winnable G D) →
  ∀ (c : Config V q) (k : ℤ),
    linear_equiv G D (c.vertex_degree + k • (one_chip q)) →
    superstable G q c →
    k < 0 := by
  intro h_not_winnable c k h_equiv h_super
  contrapose! h_not_winnable with k_nonneg
  let D' := c.vertex_degree + k • (one_chip q)
  have D'_eff : effective D' := by
    intro v
    dsimp [D']
    have c_nonneg: c.vertex_degree v ≥ 0 := c.non_negative v
    have oc_nonneg : k*one_chip q v ≥ 0 := by
      dsimp [one_chip]
      split_ifs
      · simp [k_nonneg]
      · simp
    rw [smul_apply]
    linarith
  have h_winnable_D' : winnable G D' := winnable_of_effective G D' D'_eff
  apply winnable_equiv_winnable G D' D h_winnable_D'
  apply (linear_equiv_is_equivalence G).symm h_equiv


lemma maximal_unwinnable_q_reduced_chips_at_q (G : CFGraph V) (q : V) (D : CFDiv V) :
  maximal_unwinnable G D → q_reduced G q D → D q = -1 := by
  intro h_max_unwin h_qred
  have h_neg : D q < 0 := by
    contrapose! h_max_unwin
    unfold maximal_unwinnable
    push_neg
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

-- Configuration version of the above
lemma degree_max_superstable {G : CFGraph V} {q : V} (c : Config V q) (h_max : maximal_superstable G c): config_degree c = genus G := by
  have := maximal_superstable_orientation G q c h_max
  rcases this with ⟨O, h_acyc, h_unique_source, h_orient_eq⟩
  rw [← h_orient_eq]
  rw [config_and_divisor_from_O O h_acyc h_unique_source ]
  dsimp [toConfig, config_degree]
  rw [map_sub]
  dsimp [orqed]
  rw [degree_ordiv]
  suffices (ordiv G O) q = -1 by
    rw [this]
    simp [deg_one_chip]
  -- Prove (ordiv G O) q = -1
  dsimp [ordiv]
  -- These lines look funny, but they just check that "q is a unique source" implies "q is a source."
  -- [TODO] consider making a helper lemma for this step, and/or giving a name to the "is a unique source" property.
  have := acyclic_has_source G O h_acyc
  rcases this with ⟨some_source, h_source⟩
  specialize h_unique_source some_source h_source
  rw [h_unique_source] at h_source
  dsimp [is_source] at h_source
  rw [h_source]
  norm_num

-- An odd-looking lemma, a corollary of the above, that comes in handy in some later computations.
lemma maximal_unwinnable_q_reduced_form (G : CFGraph V) (q : V) (D : CFDiv V) (c : Config V q) :
  maximal_unwinnable G D → q_reduced G q D → D = toDiv (deg D) c → D = c.vertex_degree - one_chip q := by
  intro h_max_unwinnable h_qred h_toDeg
  funext v
  by_cases hvq : q = v
  · -- Case v = q
    rw [← hvq]
    rw [maximal_unwinnable_q_reduced_chips_at_q G q D h_max_unwinnable h_qred]
    rw [sub_apply, one_chip_apply_v q, c.q_zero]
    simp
  · -- Case v ≠ q
    rw [sub_apply, one_chip_apply_other q v hvq]
    let h :=  h_toDeg
    dsimp [toDiv] at h
    apply (congrFun) at h
    specialize h v
    rw [add_apply, smul_apply] at h
    simp [h,hvq]

/-- Lemma: Superstable configuration degree is bounded by genus -/
lemma helper_superstable_degree_bound (G : CFGraph V) (q : V) (c : Config V q) :
  superstable G q c → config_degree c ≤ genus G := by
  intro h_super
  have := maximal_superstable_exists G q c h_super
  rcases this with ⟨c_max, h_maximal, h_ge_c⟩
  have h_genus_eq := degree_max_superstable c_max h_maximal
  rw [← h_genus_eq]
  dsimp [config_ge] at h_ge_c
  dsimp [config_degree]
  dsimp [deg]
  apply Finset.sum_le_sum
  intro v hv
  specialize h_ge_c v
  exact h_ge_c

lemma helper_maximal_superstable_degree_lower_bound (G : CFGraph V) (q : V) (c : Config V q) :
  superstable G q c → maximal_superstable G c → config_degree c ≥ genus G := by
  intro h_super h_max
  have := maximal_superstable_orientation G q c h_max
  rcases this with ⟨O, h_acyc, h_unique_source, h_orient_eq⟩
  have h_genus_eq : config_degree c = genus G := by
    exact degree_max_superstable c h_max
  rw [← h_genus_eq]

/-- Lemma: If a superstable configuration has degree equal to g, it is maximal -/
lemma helper_degree_g_implies_maximal (G : CFGraph V) (q : V) (c : Config V q) :
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

/-- [Proven] Proposition 4.1.13 (1): Characterization of maximal superstable configurations by their degree -/
theorem maximal_superstable_config_prop (G : CFGraph V) (q : V) (c : Config V q) :
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


lemma winnable_of_deg_ge_genus {G : CFGraph V} (h_conn : graph_connected G) (D : CFDiv V) : deg D ≥ genus G → winnable G D := by
  intro h_deg_ge_g
  let q := Classical.arbitrary V
  rcases (exists_q_reduced_representative h_conn q D) with ⟨D_qred, h_equiv, h_qred⟩
  have := (q_reduced_superstable_correspondence G q D_qred).mp h_qred
  rcases this with ⟨c, h_super, h_D_eq⟩
  have := maximal_superstable_exists G q c h_super
  rcases this with ⟨c_max, h_maximal, h_ge_c⟩
  have h_deg_c : config_degree c ≤ genus G := by
    have := degree_max_superstable c_max h_maximal
    rw [← this]
    dsimp [config_ge] at h_ge_c
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
lemma helper_maximal_superstable_chip_winnable_exact {G : CFGraph V} (h_conn : graph_connected G) (q : V) (c' : Config V q) :
  maximal_superstable G c' →
  ∀ (v : V), winnable G (c'.vertex_degree- (one_chip q) + (one_chip v)) := by
  intro h_max_superstable v
  let D' := c'.vertex_degree - one_chip q + one_chip v
  have deg_ineq : deg D' ≥ genus G := by
    dsimp [D']
    simp
    have h := degree_max_superstable c' h_max_superstable
    dsimp [config_degree] at h
    rw [h]
  exact winnable_of_deg_ge_genus h_conn D' deg_ineq


/-- [Proven] Proposition 4.1.13 (2): Characterization of maximal unwinnable divisors -/
theorem maximal_unwinnable_char {G : CFGraph V} (h_conn : graph_connected G) (q : V) (D : CFDiv V) :
  maximal_unwinnable G D ↔
  ∃ c : Config V q, maximal_superstable G c ∧
  ∃ D' : CFDiv V, q_reduced G q D' ∧ linear_equiv G D D' ∧
  D' = c.vertex_degree - one_chip q := by
  constructor
  { -- Forward direction (⇒)
    intro h_max_unwinnable_D -- Assume D is maximal unwinnable
    -- Get the unique q-reduced representative D' for D
    rcases unique_q_reduced h_conn q D with ⟨D', ⟨h_D_equiv_D', h_qred_D'⟩, _⟩
    -- Show D' corresponds to some superstable c
    rcases (q_reduced_superstable_correspondence G q D').mp h_qred_D' with ⟨c, h_super_c, h_form_D'_eq_c⟩

    -- Consider extracting this into a lemma for use elsewhere
    have h_form_D' : D' = c.vertex_degree - one_chip q := by
      apply maximal_unwinnable_q_reduced_form G q D' c _ h_qred_D' h_form_D'_eq_c
      -- Verify that D' is also maximal unwinnable
      apply maximal_unwinnable_preserved G D D' h_max_unwinnable_D h_D_equiv_D'

    -- Prove that this c must be maximal superstable
    have h_max_super_c : maximal_superstable G c := by
      -- Prove by contradiction: Assume c is not maximal superstable
      by_contra h_not_max_c
      -- If c is superstable but not maximal, there exists a strictly dominating maximal c'
      rcases maximal_superstable_exists G q c h_super_c with ⟨c', h_max_c', h_ge_c'_c⟩
      -- Define D'' based on the maximal superstable c'
      let D'' := c'.vertex_degree - one_chip q
      -- Show D'' is q-reduced (from correspondence with superstable c')
      have D''_toDiv : D'' = toDiv (deg D'') c' := by
        dsimp [toDiv,D'']
        simp [config_degree]
        rw [sub_eq_add_neg]
      have h_qred_D'' := (q_reduced_superstable_correspondence G q D'').mpr ⟨c', ⟨ h_max_c'.1, D''_toDiv⟩⟩

      -- Show D'' is also unwinnable
      have h_D''_unwinnable : ¬(winnable G D'') := by
        by_contra! h_win
        dsimp [winnable] at h_win
        rcases h_win with ⟨E, E_eff, E_equiv⟩
        let E_equiv := (linear_equiv_is_equivalence G).symm E_equiv

        have : effective D'' := helper_q_reduced_of_effective_is_effective G q E D'' E_eff E_equiv h_qred_D''
        dsimp [effective] at this
        specialize this q
        dsimp [D''] at this
        simp [c'.q_zero] at this

      -- Show D'' dominates D'
      have h_D''_ge_D' : D'' ≥ D' := by
        rw [h_form_D']; dsimp [D'']
        intro v
        simp
        -- Goal: c.vertex_degree v ≤ c'.vertex_degree v
        exact h_ge_c'_c v

      -- Deduce that D'' = D' by maximality of D'
      have h_D'_eq_D'' : D' = D'' := by
        funext v
        by_contra h_neq
        have h_strict : D'' v > D' v := lt_of_le_of_ne (h_D''_ge_D' v) h_neq
        have h_plus_one : D'' v ≥ D' v + 1 := by linarith

        have h_D''_ge_D'_plus_one : D'' ≥ D' + one_chip v := by
          intro w
          by_cases hw : w = v
          · simp [hw, h_plus_one]
          · rw [add_apply]
            simp [hw]
            exact (h_D''_ge_D' w)

        have helper : winnable G (D'' - D' - one_chip v) := by
          suffices effective (D'' - D' - one_chip v) by
            exact winnable_of_effective G (D'' - D' - one_chip v) this
          intro w
          specialize h_D''_ge_D'_plus_one w
          simp at h_D''_ge_D'_plus_one
          simp
          linarith

        have h_unwin_D'_plus_one : ¬ (winnable G (D' + one_chip v)) := by
          contrapose! h_D''_unwinnable with h_win
          have := winnable_add_winnable G (D'' - D' - one_chip v) (D' + one_chip v) helper h_win
          simp at this
          exact this

        let W := D + one_chip v
        have W_win : winnable G W := h_max_unwinnable_D.2 v
        have W_equiv_D'_plus_one : linear_equiv G W (D' + one_chip v) := by
          dsimp [linear_equiv, W]
          simp
          exact h_D_equiv_D'

        -- Contradiction: W is winnable, hence D' + one_chip v is winnable.
        apply winnable_equiv_winnable G W (D'+one_chip v)  at W_win
        exact h_unwin_D'_plus_one (W_win W_equiv_D'_plus_one)

      -- Now relate c and c' using D' = D''
      have h_lambda_eq : (c.vertex_degree - one_chip q) = (c'.vertex_degree - one_chip q) := by
        rw [← h_form_D', h_D'_eq_D'']

      -- This pointwise equality implies c = c'
      have h_c_eq_c' : c = c' := by
        -- Prove equality by showing fields are equal
        cases c; cases c' -- Expose fields vertex_degree and non_negative_except_q
        -- Use simp [mk.injEq] to reduce goal to field equality (proves non_negative_except_q equality automatically)
        simp only [Config.mk.injEq]
        -- Prove vertex_degree functions are equal using h_lambda_eq
        funext v
        have h_pointwise_eq := congr_fun h_lambda_eq v
        -- Use Int.sub_right_inj to simplify the equality
        simp at h_pointwise_eq

        -- rw [Int.sub_right_inj] at h_pointwise_eq
        exact h_pointwise_eq -- The hypothesis now matches the goal

      -- Contradiction: helper_maximal_superstable_exists implies c' ≠ c if c wasn't maximal
      have h_c_ne_c' : c ≠ c' := by
        intro hc_eq_c' -- Assume c = c' for contradiction
        -- Rewrite c' to c in the hypothesis h_max_c' using the assumed equality
        rw [← hc_eq_c'] at h_max_c'
        -- h_max_c' now has type: maximal_superstable G c ∧ config_ge c c
        -- This contradicts the initial assumption h_not_max_c (¬ maximal_superstable G c)
        exact h_not_max_c h_max_c' -- Apply h_not_max_c to the full hypothesis

      -- We derived c = c' and c ≠ c', the final contradiction
      exact h_c_ne_c' h_c_eq_c'
    -- End of by_contra proof. We now know maximal_superstable G c holds.

    -- Construct the main existential result for the forward direction
    use c, h_max_super_c -- We found the required maximal superstable c
    use D', h_qred_D', h_D_equiv_D'
    -- Show D' = form(c)
  }
  { -- Reverse direction (⇐)
    intro h_exists -- Assume the existence of c, D' with the given properties
    rcases h_exists with ⟨c, h_max_c, D', h_qred_D', h_D_equiv_D', h_form_D'_eq_c⟩

    -- Goal: Prove maximal_unwinnable G D
    constructor
    { -- Part 1: Show D is unwinnable (¬winnable G D)
      intro h_win_D -- Assume 'winnable G D' for contradiction
      -- Use linear equivalence to transfer winnability from D to D'
      have h_win_D' : winnable G D' :=
        winnable_equiv_winnable G D D' h_win_D h_D_equiv_D'

      -- The divisor form derived from a maximal superstable config is unwinnable
      have h_unwin_form : ¬(winnable G (λ v => c.vertex_degree v - if v = q then 1 else 0)) :=
        helper_superstable_to_unwinnable h_conn q c h_max_c

      -- Since D' equals this form, D' is unwinnable
      have h_unwin_D' : ¬(winnable G D') := by
        rw [h_form_D'_eq_c] -- Rewrite goal to use the form
        exact h_unwin_form -- Apply the unwinnability of the form

      -- Contradiction between h_win_D' and h_unwin_D'
      exact h_unwin_D' h_win_D'
    }
    { -- Part 2: Show D + δᵥ is winnable for any v (∀ v, winnable G (D + δᵥ))
      intro v -- Take an arbitrary vertex v

      -- Define the divisor form associated with c and the form plus δᵥ
      let D'_form : CFDiv V := λ w => c.vertex_degree w - if w = q then (1 : ℤ) else (0 : ℤ)
      let delta_v : CFDiv V := fun w => ite (w = v) 1 0
      let D'_form_plus_delta_v := D'_form + delta_v

      -- Adding a chip to the form derived from a maximal superstable config makes it winnable
      have h_win_D'_form_plus_delta_v : winnable G D'_form_plus_delta_v :=
        helper_maximal_superstable_chip_winnable_exact h_conn q c h_max_c v

      -- Define D + δᵥ
      let D_plus_delta_v := D + delta_v

      -- Show that D + δᵥ is linearly equivalent to D' + δᵥ (which equals D'_form + δᵥ)
      have h_equiv_plus_delta : linear_equiv G D_plus_delta_v D'_form_plus_delta_v := by
        -- Goal: (D'_form + delta_v) - (D + delta_v) ∈ P
        unfold linear_equiv -- Explicitly unfold goal
        -- Simplify the difference using group properties
        have h_diff_simp : (D'_form + delta_v) - (D + delta_v) = D'_form - D := by
           funext w; simp only [add_apply, sub_apply]; ring -- Pointwise proof (use funext)
        rw [h_diff_simp] -- Apply simplification
        -- Goal: D'_form - D ∈ P
        -- We know D' - D ∈ P (from h_D_equiv_D')
        unfold linear_equiv at h_D_equiv_D'
        -- We know D' = D'_form (by h_form_D'_eq_c)
        rw [h_form_D'_eq_c] at h_D_equiv_D' -- Rewrite D' as D'_form in h_D_equiv_D'
        exact h_D_equiv_D' -- Use the rewritten hypothesis

      -- Since D + δᵥ is linearly equivalent to a winnable divisor (D'_form + δᵥ), it must be winnable.
      apply winnable_equiv_winnable G D'_form_plus_delta_v D_plus_delta_v h_win_D'_form_plus_delta_v
      exact (linear_equiv_is_equivalence G).symm h_equiv_plus_delta
    }
  }

/-- [Proven] Proposition 4.1.13: Combined (1) and (2)-/
theorem superstable_and_maximal_unwinnable {G : CFGraph V} (h_conn : graph_connected G) (q : V)
    (c : Config V q) (D : CFDiv V) :
    (superstable G q c →
     (maximal_superstable G c ↔ config_degree c = genus G)) ∧
    (maximal_unwinnable G D ↔
     ∃ c : Config V q, maximal_superstable G c ∧
     ∃ D' : CFDiv V, q_reduced G q D' ∧ linear_equiv G D D' ∧
     D' = λ v => c.vertex_degree v - if v = q then 1 else 0) := by
  -- This theorem now just wraps the two proven theorems above
  exact ⟨maximal_superstable_config_prop G q c,
         maximal_unwinnable_char h_conn q D⟩

/-- Theorem: A maximal unwinnable divisor has degree g-1
    This theorem now proven based on the characterizations above. -/
theorem maximal_unwinnable_deg
  {G : CFGraph V} (h_conn : graph_connected G) (D : CFDiv V) :
  maximal_unwinnable G D → deg D = genus G - 1 := by
  intro h_max_unwin

  let q := Classical.arbitrary V

  have h_equiv_max_unwin := maximal_unwinnable_char h_conn q D
  rcases h_equiv_max_unwin.mp h_max_unwin with ⟨c, h_c_max_super, D', h_D'_qred, h_equiv_D_D', h_D'_eq⟩

  have h_c_super : superstable G q c := h_c_max_super.1

  -- Use the characterization theorem for config degree
  have h_config_deg : config_degree c = genus G := by
    have prop := maximal_superstable_config_prop G q c h_c_super -- Apply hypothesis first
    exact prop.mp h_c_max_super -- Use the forward direction of the iff

  have h_deg_D' : deg D' = genus G - 1 := calc
    deg D' = deg (c.vertex_degree - one_chip q) := by
      rw [h_D'_eq]
    -- _ = (∑ v, c.vertex_degree v) - (∑ v, if v = q then 1 else 0) := by

    --   dsimp [deg]
    --   rw [Finset.sum_sub_distrib]

    _ = (∑ v, c.vertex_degree v) - 1 := by --{rw [Finset.sum_ite_eq']; simp}
      rw [map_sub, deg_one_chip]
      simp [deg]
    _ = (config_degree c + c.vertex_degree q) - 1 := by
        have h_sum_c : ∑ v : V, c.vertex_degree v = config_degree c + c.vertex_degree q := by
          unfold config_degree
          rw [c.q_zero]
          simp [deg]
        rw [h_sum_c]
    _ = genus G - 1 := by
        -- Since c is maximal superstable, it corresponds to an orientation
        rcases maximal_superstable_orientation G q c h_c_max_super with
          ⟨O, h_acyc, h_unique_source, h_c_eq_orient_config⟩

        -- The configuration derived from an orientation has 0 at q
        have h_orient_config_q_zero : (orientation_to_config G O q h_acyc h_unique_source).vertex_degree q = 0 := by
          unfold orientation_to_config config_of_source
          simp

        -- Thus, c must have 0 at q
        have h_c_q_zero : c.vertex_degree q = 0 := by
          -- First establish equality of the vertex_degree functions using structure equality
          have h_vertex_degree_eq : c.vertex_degree = (orientation_to_config G O q h_acyc h_unique_source).vertex_degree := by
            rw [h_c_eq_orient_config] -- This leaves the goal c.vertex_degree = c.vertex_degree which is true by reflexivity
          -- Apply the function equality at vertex q
          have h_eq_at_q := congr_fun h_vertex_degree_eq q
          -- Rewrite the RHS of h_eq_at_q using the known value (0)
          rw [h_orient_config_q_zero] at h_eq_at_q
          -- The result is the desired equality
          exact h_eq_at_q

        -- Now substitute known values into the expression
        rw [h_config_deg, h_c_q_zero] -- config_degree c = genus G and c.vertex_degree q = 0
        simp -- genus G + 0 - 1 = genus G - 1

  have h_deg_eq : deg D = deg D' := linear_equiv_preserves_deg G D D' h_equiv_D_D'
  rw [h_deg_eq, h_deg_D']

/-- [Proven] Proposition 4.1.14: Key results about maximal unwinnable divisors:
    1) There is an injection from acyclic orientations with source q to maximal unwinnable q-reduced divisors,
       where an orientation O maps to the divisor D(O) - q where D(O) assigns indegree to each vertex. (Surjection proof deferred)
    2) Any maximal unwinnable divisor has degree equal to genus - 1. -/
theorem acyclic_orientation_maximal_unwinnable_correspondence_and_degree
    {G : CFGraph V} (h_conn : graph_connected G) (q : V) :
    (Function.Injective (λ (O : {O : CFOrientation G // is_acyclic G O ∧ is_source G O q}) =>
      λ v => (indeg G O.val v) - if v = q then 1 else 0)) ∧
    (∀ D : CFDiv V, maximal_unwinnable G D → deg D = genus G - 1) := by
  constructor
  { -- Part 1: Injection proof
    intros O₁ O₂ h_eq
    have h_indeg : ∀ v : V, indeg G O₁.val v = indeg G O₂.val v := by
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






/-
## The main Riemann-Roch inequality.
-/

/-- [Proven] Rank Degree Inequality -/
theorem rank_degree_inequality
    {G : CFGraph V} (h_conn : graph_connected G) (D : CFDiv V) :
    deg D - genus G < rank G D - rank G (canonical_divisor G - D) := by
  -- Get rank value for D
  let r := rank G D

  -- Get effective divisor E using rank characterization
  rcases rank_get_effective G D with ⟨E, h_E_eff, h_E_deg, h_D_E_unwin⟩

  -- Fix a vertex q
  let q := Classical.arbitrary V

  -- Apply Dhar's algorithm to D - E to get q-reduced form
  rcases superstable_of_divisor h_conn q (D - E) with ⟨c, k, h_equiv, h_super⟩

  have h_k_neg := superstable_of_divisor_negative_k G q (D - E) h_D_E_unwin c k h_equiv h_super

  -- Get maximal superstable c' ≥ c
  rcases maximal_superstable_exists G q c h_super with ⟨c', h_max', h_ge⟩

  -- Let O be corresponding acyclic orientation using the bijection
  rcases orientation_superstable_bijection G q with ⟨_, h_surj⟩
  -- Apply h_surj to the subtype element ⟨c', h_max'⟩
  rcases h_surj ⟨c', h_max'⟩ with ⟨O_subtype, h_eq_c'⟩ -- O_subtype is {O // acyclic ∧ unique_source}
  let O := O_subtype.val
  let O_acyc := O_subtype.prop.1
  let O_unique_source := O_subtype.prop.2

  -- Get configuration c' from orientation O_subtype
  -- O_subtype.val is the CFOrientation, O_subtype.prop.1 is acyclicity, O_subtype.prop.2 is uniqueness
  let c'_config := orientation_to_config G O q O_acyc O_unique_source

  -- Check consistency: h_eq_c' implies c'_config = c'
  have h_orient_eq_c' : c'_config = c' := by exact Subtype.mk.inj h_eq_c'

  -- Check consistency (assuming h_eq_c' implies c' = c'_config)
  -- Define H := (c' - c) - (k + 1)q as a divisor (using original c')
  let H : CFDiv V := -(k+1) • (one_chip q) + c'.vertex_degree - c.vertex_degree

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
    have := (Eff V).add_mem src_eff diff_eff
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
    have c'_eq : c' = toConfig (orqed O O_acyc O_unique_source) := by
      rw [← h_orient_eq_c']
      dsimp [c'_config]
      rw [config_and_divisor_from_O O O_acyc O_unique_source]

    have : toDiv (genus G - 1) (toConfig (orqed O O_acyc O_unique_source)) = ordiv G O := by
      have := div_of_config_of_div (orqed O O_acyc O_unique_source)
      dsimp [orqed] at *
      rw [degree_ordiv O] at this
      exact this
    rw [← this]
    dsimp [M,toDiv]
    rw [c'_eq]
    have : (genus G - 1 - config_degree (toConfig (orqed O O_acyc O_unique_source))) = -1 := by
      dsimp [config_degree]
      have := config_degree_div_degree (orqed O O_acyc O_unique_source)
      dsimp [orqed] at this
      rw [degree_ordiv O] at this
      rw [this]
      dsimp [config_degree, toConfig]
      rw [map_sub, map_sub]
      dsimp [orqed]
      simp [degree_ordiv O]
      -- Now just show ordiv has degree -1 at source
      -- This is surely proved somewhere already??
      dsimp [ordiv]
      suffices is_source G O q by
        dsimp [is_source] at this
        rw [this]; simp
      -- Show q is a source in O... [TODO] bubble this off as a lemma
      rcases acyclic_has_source G O O_acyc with ⟨s, hs⟩
      specialize O_unique_source s hs
      rw [O_unique_source] at hs
      exact hs
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
