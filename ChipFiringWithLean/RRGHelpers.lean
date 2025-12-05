import ChipFiringWithLean.Basic
import ChipFiringWithLean.Config
import ChipFiringWithLean.Orientation
import ChipFiringWithLean.Rank
import ChipFiringWithLean.Helpers
import Mathlib.Algebra.Ring.Int
import Paperproof

set_option linter.unusedVariables false
set_option trace.split.failure true

open Multiset Finset

-- Assume V is a finite type with decidable equality
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]

-- [Proven] Lemma: effectiveness is preserved under legal firing (Additional)
lemma legal_firing_preserves_effective (G : CFGraph V) (D : CFDiv V) (S : Finset V) :
  legal_set_firing G D S → effective D → effective (set_firing G D S) := by
  intros h_legal h_eff v
  simp [set_firing]
  by_cases hv : v ∈ S
  -- Case 1: v ∈ S
  · exact h_legal v hv
  -- Case 2: v ∉ S
  · have h1 : D v ≥ 0 := h_eff v
    have h2 : finset_sum S (λ v' => if v = v' then -vertex_degree G v' else num_edges G v' v) ≥ 0 := by
      apply Finset.sum_nonneg
      intro x hx
      -- Split on whether v = x
      by_cases hveq : v = x
      · -- If v = x, contradiction with v ∉ S
        rw [hveq] at hv
        contradiction
      · -- If v ≠ x, then we get num_edges which is non-negative
        simp [hveq]
    exact add_nonneg h1 h2

-- [Proven] Proposition 3.2.4: q-reduced and effective implies winnable
theorem winnable_iff_q_reduced_effective (G : CFGraph V) (q : V) (D : CFDiv V) :
  winnable G D ↔ ∃ D' : CFDiv V, linear_equiv G D D' ∧ q_reduced G q D' ∧ effective D' := by
  constructor
  { -- Forward direction
    intro h_win
    rcases h_win with ⟨E, h_eff, h_equiv⟩
    rcases helper_unique_q_reduced G q D with ⟨D', h_D'⟩
    use D'
    constructor
    · exact h_D'.1.1  -- D is linearly equivalent to D'
    constructor
    · exact h_D'.1.2  -- D' is q-reduced
    · -- Show D' is effective using:
      -- First get E ~ D' by transitivity through D
      have h_equiv_symm : linear_equiv G E D := (linear_equiv_is_equivalence G).symm h_equiv -- E ~ D
      have h_equiv_E_D' : linear_equiv G E D' := (linear_equiv_is_equivalence G).trans h_equiv_symm h_D'.1.1 -- E ~ D ~ D' => E ~ D'
      -- Now use the axiom that q-reduced form of an effective divisor is effective
      exact helper_q_reduced_of_effective_is_effective G q E D' h_eff h_equiv_E_D' h_D'.1.2
  }
  { -- Reverse direction
    intro h
    rcases h with ⟨D', h_equiv, h_qred, h_eff⟩
    use D'
    exact ⟨h_eff, h_equiv⟩
  }

-- [Proven] Proposition 3.2.4 (Extension): q-reduced and effective implies winnable
theorem q_reduced_effective_implies_winnable (G : CFGraph V) (q : V) (D : CFDiv V) :
  q_reduced G q D → effective D → winnable G D := by
  intros h_qred h_eff
  -- Apply right direction of iff
  rw [winnable_iff_q_reduced_effective]
  -- Prove existence
  use D
  constructor
  · exact (linear_equiv_is_equivalence G).refl D  -- D is linearly equivalent to itself using proven reflexivity
  constructor
  · exact h_qred  -- D is q-reduced
  · exact h_eff   -- D is effective

/-- [Proven] Lemma 4.1.10: An acyclic orientation is uniquely determined by its indegree sequence -/
theorem acyclic_orientation_unique_by_indeg {G : CFGraph V}
  (O O' : CFOrientation G)
  (h_acyclic : is_acyclic G O)
  (h_acyclic' : is_acyclic G O')
  (h_indeg : ∀ v : V, indeg G O v = indeg G O' v) :
  O = O' := by
  -- Apply the helper_orientation_determined_by_levels axiom directly
  exact helper_orientation_determined_by_levels O O' h_acyclic h_acyclic' h_indeg

/-- [Proven] Lemma 4.1.10 (Alternative Form): Two acyclic orientations with same indegree sequences are equal -/
theorem acyclic_equal_of_same_indeg {G : CFGraph V} (O O' : CFOrientation G)
    (h_acyclic : is_acyclic G O) (h_acyclic' : is_acyclic G O')
    (h_indeg : ∀ v : V, indeg G O v = indeg G O' v) :
    O = O' := by
  -- Use previously defined theorem about uniqueness by indegree
  exact acyclic_orientation_unique_by_indeg O O' h_acyclic h_acyclic' h_indeg

/-- [Proven] Proposition 4.1.11: Bijection between acyclic orientations with source q
    and maximal superstable configurations -/
theorem stable_bijection (G : CFGraph V) (q : V) :
    let α := {O : CFOrientation G // is_acyclic G O ∧ (∀ w, is_source G O w → w = q)};
    let β := {c : Config V q // maximal_superstable G c};
    let f_raw : α → Config V q := λ O_sub => orientation_to_config G O_sub.val q O_sub.prop.1 O_sub.prop.2;
    let f : α → β := λ O_sub => ⟨f_raw O_sub, helper_orientation_config_maximal G O_sub.val q O_sub.prop.1 O_sub.prop.2⟩;
    Function.Bijective f := by
  -- Define the domain and codomain types explicitly (can be removed if using let like above)
  let α := {O : CFOrientation G // is_acyclic G O ∧ (∀ w, is_source G O w → w = q)}
  let β := {c : Config V q // maximal_superstable G c}
  -- Define the function f_raw : α → Config V q
  let f_raw : α → Config V q := λ O_sub => orientation_to_config G O_sub.val q O_sub.prop.1 O_sub.prop.2
  -- Define the function f : α → β, showing the result is maximal superstable
  let f : α → β := λ O_sub =>
    ⟨f_raw O_sub, helper_orientation_config_maximal G O_sub.val q O_sub.prop.1 O_sub.prop.2⟩

  constructor
  -- Injectivity
  { -- Prove injective f using injective f_raw
    intros O₁_sub O₂_sub h_f_eq -- h_f_eq : f O₁_sub = f O₂_sub
    have h_f_raw_eq : f_raw O₁_sub = f_raw O₂_sub := by simp [f] at h_f_eq; exact h_f_eq

    -- Reuse original injectivity proof structure, ensuring types match
    let ⟨O₁, h₁⟩ := O₁_sub
    let ⟨O₂, h₂⟩ := O₂_sub
    -- Define c, h_eq₁, h_eq₂ based on orientation_to_config directly
    let c := orientation_to_config G O₁ q h₁.1 h₁.2
    have h_eq₁ : orientation_to_config G O₁ q h₁.1 h₁.2 = c := rfl
    have h_eq₂ : orientation_to_config G O₂ q h₂.1 h₂.2 = c := by
      exact h_f_raw_eq.symm.trans h_eq₁ -- Use transitivity

    have h_src₁ : is_source G O₁ q := by
      rcases helper_acyclic_has_source G O₁ h₁.1 with ⟨s, hs⟩; have h_s_eq_q : s = q := h₁.2 s hs; rwa [h_s_eq_q] at hs
    have h_src₂ : is_source G O₂ q := by
      rcases helper_acyclic_has_source G O₂ h₂.1 with ⟨s, hs⟩; have h_s_eq_q : s = q := h₂.2 s hs; rwa [h_s_eq_q] at hs

    -- Define h_super and h_max in terms of c
    have h_super : superstable G q c := by
      rw [← h_eq₁]; exact helper_orientation_config_superstable G O₁ q h₁.1 h₁.2
    have h_max   : maximal_superstable G c := by
      rw [← h_eq₁]; exact helper_orientation_config_maximal G O₁ q h₁.1 h₁.2

    apply Subtype.eq
    -- Call helper_config_to_orientation_unique with the original h_eq₁ and h_eq₂
    exact (helper_config_to_orientation_unique G q c h_super h_max
      O₁ O₂ h₁.1 h₂.1 h_src₁ h_src₂ h₁.2 h₂.2 h_eq₁ h_eq₂)
  }

  -- Surjectivity
  { -- Prove Function.Surjective f
    unfold Function.Surjective
    intro y -- y should now have type β
    -- Access components using .val and .property
    let c_target : Config V q := y.val -- Explicitly type c_target
    let h_target_max_superstable := y.property

    -- Use the axiom that every maximal superstable config comes from an orientation.
    rcases helper_maximal_superstable_orientation G q c_target h_target_max_superstable with
      ⟨O, h_acyc, h_unique_source, h_config_eq_target⟩

    -- Construct the required subtype element x : α (the pre-image)
    let x : α := ⟨O, ⟨h_acyc, h_unique_source⟩⟩

    -- Show that this x exists
    use x

    -- Show f x = y using Subtype.eq
    apply Subtype.eq
    -- Goal: (f x).val = y.val
    -- Need to show: f_raw x = c_target
    -- This is exactly h_config_eq_target
    exact h_config_eq_target
    -- Proof irrelevance handles the equality of the property components.
  }

/-- [Proven] Proposition 4.1.13 (1): Characterization of maximal superstable configurations by their degree -/
theorem maximal_superstable_config_prop (G : CFGraph V) (q : V) (c : Config V q) :
  superstable G q c → (maximal_superstable G c ↔ config_degree c = genus G) := by
  intro h_super
  constructor
  { -- Forward direction: maximal_superstable → degree = g
    intro h_max
    -- Use degree bound and maximality
    have h_bound := helper_superstable_degree_bound G q c h_super
    have h_geq := helper_maximal_superstable_degree_lower_bound G q c h_super h_max
    -- Combine bounds to get equality
    exact le_antisymm h_bound h_geq }
  { -- Reverse direction: degree = g → maximal_superstable
    intro h_deg
    -- Apply the axiom that degree g implies maximality
    exact helper_degree_g_implies_maximal G q c h_super h_deg }

/-- [Proven] Proposition 4.1.13 (2): Characterization of maximal unwinnable divisors -/
theorem maximal_unwinnable_char (G : CFGraph V) (q : V) (D : CFDiv V) :
  maximal_unwinnable G D ↔
  ∃ c : Config V q, maximal_superstable G c ∧
  ∃ D' : CFDiv V, q_reduced G q D' ∧ linear_equiv G D D' ∧
  D' = λ v => c.vertex_degree v - if v = q then 1 else 0 := by
  constructor
  { -- Forward direction (⇒)
    intro h_max_unwinnable_D -- Assume D is maximal unwinnable
    -- Get the unique q-reduced representative D' for D
    rcases helper_unique_q_reduced G q D with ⟨D', ⟨h_D_equiv_D', h_qred_D'⟩, _⟩
    -- Show D' corresponds to some superstable c
    rcases (q_reduced_superstable_correspondence G q D').mp h_qred_D' with ⟨c, h_super_c, h_form_D'_eq_c⟩

    -- Prove that this c must be maximal superstable
    have h_max_super_c : maximal_superstable G c := by
      -- Prove by contradiction: Assume c is not maximal superstable
      by_contra h_not_max_c
      -- If c is superstable but not maximal, there exists a strictly dominating maximal c'
      rcases helper_maximal_superstable_exists G q c h_super_c with ⟨c', h_max_c', h_ge_c'_c⟩
      -- Define D'' based on the maximal superstable c'
      let D'' := λ v => c'.vertex_degree v - if v = q then (1 : ℤ) else (0 : ℤ)
      -- Show D'' is q-reduced (from correspondence with superstable c')
      have h_qred_D'' := (q_reduced_superstable_correspondence G q D'').mpr ⟨c', h_max_c'.1, rfl⟩

      -- Show D' is linearly equivalent to D''
      have h_D'_equiv_D'' : linear_equiv G D' D'' := by
        -- We know D' = form(c) (h_form_D'_eq_c)
        -- We know form(c) ~ form(c') = D'' (helper_q_reduced_linear_equiv_dominates)
        rw [h_form_D'_eq_c] -- Replace D' with form(c)
        exact helper_q_reduced_linear_equiv_dominates G q c c' h_super_c h_max_c'.1 h_ge_c'_c

      -- Since D' and D'' are both q-reduced and linearly equivalent, they must be equal
      have h_D'_eq_D'' : D' = D'' := by
        apply q_reduced_unique G q D' D''
        -- Provide the triple ⟨q_reduced D', q_reduced D'', D' ~ D''⟩
        exact ⟨h_qred_D', h_qred_D'', h_D'_equiv_D''⟩

      -- Now relate c and c' using D' = D''
      have h_lambda_eq : (λ v => c.vertex_degree v - if v = q then 1 else 0) = (λ v => c'.vertex_degree v - if v = q then 1 else 0) := by
        rw [← h_form_D'_eq_c] -- LHS = D'
        rw [h_D'_eq_D'']      -- Goal: D'' = RHS

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
        rw [Int.sub_right_inj] at h_pointwise_eq
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
    use D', h_qred_D', h_D_equiv_D', h_form_D'_eq_c -- Use the q-reduced D' and its properties
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
        (helper_linear_equiv_preserves_winnability G D D' h_D_equiv_D').mp h_win_D

      -- The divisor form derived from a maximal superstable config is unwinnable
      have h_unwin_form : ¬(winnable G (λ v => c.vertex_degree v - if v = q then 1 else 0)) :=
        helper_superstable_to_unwinnable G q c h_max_c

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
        helper_maximal_superstable_chip_winnable_exact G q c h_max_c v

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
      exact (helper_linear_equiv_preserves_winnability G D_plus_delta_v D'_form_plus_delta_v h_equiv_plus_delta).mpr h_win_D'_form_plus_delta_v
    }
  }

/-- [Proven] Proposition 4.1.13: Combined (1) and (2)-/
theorem superstable_and_maximal_unwinnable (G : CFGraph V) (q : V)
    (c : Config V q) (D : CFDiv V) :
    (superstable G q c →
     (maximal_superstable G c ↔ config_degree c = genus G)) ∧
    (maximal_unwinnable G D ↔
     ∃ c : Config V q, maximal_superstable G c ∧
     ∃ D' : CFDiv V, q_reduced G q D' ∧ linear_equiv G D D' ∧
     D' = λ v => c.vertex_degree v - if v = q then 1 else 0) := by
  -- This theorem now just wraps the two proven theorems above
  exact ⟨maximal_superstable_config_prop G q c,
         maximal_unwinnable_char G q D⟩

/-- Theorem: A maximal unwinnable divisor has degree g-1
    This theorem now proven based on the characterizations above. -/
theorem maximal_unwinnable_deg
  (G : CFGraph V) (D : CFDiv V) :
  maximal_unwinnable G D → deg D = genus G - 1 := by
  intro h_max_unwin

  let q := Classical.arbitrary V

  have h_equiv_max_unwin := maximal_unwinnable_char G q D
  rcases h_equiv_max_unwin.mp h_max_unwin with ⟨c, h_c_max_super, D', h_D'_qred, h_equiv_D_D', h_D'_eq⟩

  have h_c_super : superstable G q c := h_c_max_super.1

  -- Use the characterization theorem for config degree
  have h_config_deg : config_degree c = genus G := by
    have prop := maximal_superstable_config_prop G q c h_c_super -- Apply hypothesis first
    exact prop.mp h_c_max_super -- Use the forward direction of the iff

  have h_deg_D' : deg D' = genus G - 1 := calc
    deg D' = deg (λ v => c.vertex_degree v - if v = q then 1 else 0) := by rw [h_D'_eq]
    _ = (∑ v, c.vertex_degree v) - (∑ v, if v = q then 1 else 0) := by {unfold deg; rw [Finset.sum_sub_distrib]}
    _ = (∑ v, c.vertex_degree v) - 1 := by {rw [Finset.sum_ite_eq']; simp}
    _ = (config_degree c + c.vertex_degree q) - 1 := by
        have h_sum_c : ∑ v : V, c.vertex_degree v = config_degree c + c.vertex_degree q := by
          unfold config_degree
          rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := λ v' => v' ≠ q)] -- Split sum based on v ≠ q
          simp [Finset.sum_singleton, Finset.filter_eq'] -- Add Finset.filter_eq' hint
        rw [h_sum_c]
    _ = genus G - 1 := by
        -- Since c is maximal superstable, it corresponds to an orientation
        rcases helper_maximal_superstable_orientation G q c h_c_max_super with
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
    (G : CFGraph V) (q : V) :
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
      · exact helper_source_indeg_eq_at_q G O₁.val O₂.val q v O₁.prop.2 O₂.prop.2 hv
      · simp [hv] at this
        exact this
    exact Subtype.ext (acyclic_orientation_unique_by_indeg O₁.val O₂.val O₁.prop.1 O₂.prop.1 h_indeg)
  }
  { -- Part 2: Degree characterization
    -- This now correctly refers to the theorem defined above
    intro D hD
    exact maximal_unwinnable_deg G D hD
  }

/-- [Proven] Corollary 4.2.2: Rank inequality for divisors -/
theorem rank_subadditive (G : CFGraph V) (D D' : CFDiv V)
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
    have h := helper_winnable_add G (D-E₁) (D'-E₂) h_D_win h_D'_win
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

-- [Proven] Corollary 4.2.3: Degree of canonical divisor equals 2g - 2
theorem degree_of_canonical_divisor (G : CFGraph V) :
    deg (canonical_divisor G) = 2 * genus G - 2 := by
  -- First unfold definitions
  unfold deg canonical_divisor

  -- Use sum_sub_distrib to split the sum
  have h1 : ∑ v, (vertex_degree G v - 2) =
            ∑ v, vertex_degree G v - 2 * Fintype.card V := by
    rw [sum_sub_distrib]
    simp [sum_const, nsmul_eq_mul]
    ring

  rw [h1]

  -- Use the fact that sum of vertex degrees = 2|E|
  have h2 : ∑ v, vertex_degree G v = 2 * Multiset.card G.edges := by
    exact helper_sum_vertex_degrees G
  rw [h2]

  -- Use genus definition: g = |E| - |V| + 1
  rw [genus]

  ring

/-- [Proven] Rank Degree Inequality -/
theorem rank_degree_inequality
    (G : CFGraph V) (D : CFDiv V) :
    deg D - genus G < rank G D - rank G (λ v => canonical_divisor G v - D v) := by
  -- Get rank value for D
  let r := rank G D

  -- Get effective divisor E using rank characterization
  rcases rank_get_effective G D with ⟨E, h_E_eff, h_E_deg, h_D_E_unwin⟩

  -- Fix a vertex q
  let q := Classical.arbitrary V

  -- Apply Dhar's algorithm to D - E to get q-reduced form
  rcases helper_dhar_algorithm G q (λ v => D v - E v) with ⟨c, k, h_equiv, h_super⟩

  -- k must be negative since D - E is unwinnable
  have h_k_neg := helper_dhar_negative_k G q (λ v => D v - E v) h_D_E_unwin c k h_equiv h_super

  -- Get maximal superstable c' ≥ c
  rcases helper_maximal_superstable_exists G q c h_super with ⟨c', h_max', h_ge⟩

  -- Let O be corresponding acyclic orientation using the bijection
  rcases stable_bijection G q with ⟨h_inj, h_surj⟩
  -- Apply h_surj to the subtype element ⟨c', h_max'⟩
  rcases h_surj ⟨c', h_max'⟩ with ⟨O_subtype, h_eq_c'⟩ -- O_subtype is {O // acyclic ∧ unique_source}

  -- Get configuration c' from orientation O_subtype
  -- O_subtype.val is the CFOrientation, O_subtype.prop.1 is acyclicity, O_subtype.prop.2 is uniqueness
  let c'_config := orientation_to_config G O_subtype.val q O_subtype.prop.1 O_subtype.prop.2

  -- Check consistency: h_eq_c' implies c'_config = c'
  have h_orient_eq_c' : c'_config = c' := by exact Subtype.mk.inj h_eq_c'

  -- Check consistency (assuming h_eq_c' implies c' = c'_config)
  -- Define H := (c' - c) - (k + 1)q as a divisor (using original c')
  let H : CFDiv V := λ v =>
    if v = q then -(k + 1)
    else c'.vertex_degree v - c.vertex_degree v

  have h_H_eff : effective H := by
    intro v
    by_cases h_v : v = q
    · -- Case v = q
      rw [h_v]
      simp [H]
      -- Since k < 0, k + 1 ≤ 0, so -(k + 1) ≥ 0
      have h_k_plus_one_nonpos : k + 1 ≤ 0 := by
        linarith [h_k_neg]
      linarith

    · -- Case v ≠ q
      simp [H, h_v]
      -- h_ge shows c' ≥ c for maximal superstable c'
      have h_ge_at_v : c'.vertex_degree v ≥ c.vertex_degree v := by
        exact h_ge v
      -- Therefore difference is non-negative
      linarith

  -- Complete h_DO_unwin
  have h_DO_unwin : maximal_unwinnable G (λ v => c'.vertex_degree v - if v = q then 1 else 0) := by
    constructor
    · -- First show it's unwinnable
      exact helper_superstable_to_unwinnable G q c' h_max'

    · -- Then show adding a chip anywhere makes it winnable
      exact helper_maximal_superstable_chip_winnable_exact G q c' h_max'

  -- Use degree property of maximal unwinnable divisors
  have h_DO_deg : deg (λ v => c'.vertex_degree v - if v = q then 1 else 0) = genus G - 1 :=
    maximal_unwinnable_deg G _ h_DO_unwin

  calc deg D - genus G
    _ = deg D - (Multiset.card G.edges - Fintype.card V + 1) := by rw [genus]
    _ < deg D - deg E + deg H := by
        -- Substitute deg E = rank G D + 1
        rw [h_E_deg]
        -- Goal simplifies to: rank G D + 1 - genus G < deg H
        -- Apply the axiom to get this inequality as a hypothesis
        have h_bound := helper_H_degree_bound G q D H k c c' h_H_eff (by simp [H]) -- Provide proof for H form
        -- Show the original goal follows algebraically
        linarith [h_bound]
    _ ≤ rank G D - rank G (λ v => canonical_divisor G v - D v) := by
        -- This inequality is helper_rank_deg_canonical_bound rearranged
        apply le_sub_iff_add_le.mpr
        -- Provide the axiom conclusion and let linarith handle rearrangement
        have h_bound_orig := helper_rank_deg_canonical_bound G q D E H c' (helper_DO_linear_equiv G q D E H c')
        linarith [h_bound_orig]
