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
  D' = c.vertex_degree - one_chip q := by
  constructor
  { -- Forward direction (⇒)
    intro h_max_unwinnable_D -- Assume D is maximal unwinnable
    -- Get the unique q-reduced representative D' for D
    rcases helper_unique_q_reduced G q D with ⟨D', ⟨h_D_equiv_D', h_qred_D'⟩, _⟩
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
      rcases helper_maximal_superstable_exists G q c h_super_c with ⟨c', h_max_c', h_ge_c'_c⟩
      -- Define D'' based on the maximal superstable c'
      let D'' := c'.vertex_degree - one_chip q
      -- Show D'' is q-reduced (from correspondence with superstable c')
      have D''_toDiv : D'' = toDiv (deg D'') c' := by
        dsimp [toDiv,D'']
        simp [c'.q_zero, config_degree]
        rw [sub_eq_add_neg]
      have h_qred_D'' := (q_reduced_superstable_correspondence G q D'').mpr ⟨c', ⟨ h_max_c'.1, D''_toDiv⟩⟩

      -- Show D'' is also unwinnable
      have h_D''_unwinnable : ¬(winnable G D'') := by
        by_contra! h_win
        dsimp [winnable] at h_win
        rcases h_win with ⟨E, E_eff, E_equiv⟩
        let E_equiv := (linear_equiv_is_equivalence G).symmetric E_equiv

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
        rw [helper_linear_equiv_preserves_winnability G W (D' + one_chip v) W_equiv_D'_plus_one] at W_win
        exact h_unwin_D'_plus_one W_win

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
        simp [map_sub] at h_pointwise_eq

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

-- [Proven] Corollary 4.2.3: Degree of canonical divisor equals 2g - 2
theorem degree_of_canonical_divisor (G : CFGraph V) :
    deg (canonical_divisor G) = 2 * genus G - 2 := by
  -- Use sum_sub_distrib to split the sum
  have h1 : ∑ v, (canonical_divisor G v) =
            ∑ v, vertex_degree G v - 2 * Fintype.card V := by
    unfold canonical_divisor
    rw [sum_sub_distrib]
    simp [sum_const, nsmul_eq_mul]
    ring
  dsimp [deg]
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
    deg D - genus G < rank G D - rank G (canonical_divisor G - D) := by
  -- Get rank value for D
  let r := rank G D

  -- Get effective divisor E using rank characterization
  rcases rank_get_effective G D with ⟨E, h_E_eff, h_E_deg, h_D_E_unwin⟩

  -- Fix a vertex q
  let q := Classical.arbitrary V

  -- Apply Dhar's algorithm to D - E to get q-reduced form
  rcases helper_dhar_algorithm G q (D - E) with ⟨c, k, h_equiv, h_super⟩

  have h_k_neg := helper_dhar_negative_k G q (D - E) h_D_E_unwin c k h_equiv h_super

  -- Get maximal superstable c' ≥ c
  rcases helper_maximal_superstable_exists G q c h_super with ⟨c', h_max', h_ge⟩

  -- Let O be corresponding acyclic orientation using the bijection
  rcases stable_bijection G q with ⟨_, h_surj⟩
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
    have := eff_of_eff_add_eff _ _ src_eff diff_eff
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
      simp [degree_ordiv O, map_smul]
      -- Now just show ordiv has degree -1 at source
      -- This is surely proved somewhere already??
      dsimp [ordiv]
      suffices is_source G O q by
        dsimp [is_source] at this
        simp at this
        rw [this]; simp
      -- Show q is a source in O... [TODO] bubble this off as a lemma
      rcases helper_acyclic_has_source G O O_acyc with ⟨s, hs⟩
      specialize O_unique_source s hs
      rw [O_unique_source] at hs
      exact hs
    simp [this]
    rw [sub_eq_add_neg]

  -- Complete h_DO_unwin
  have h_DO_unwin : maximal_unwinnable G M := by
    constructor
    · -- First show it's unwinnable
      exact helper_superstable_to_unwinnable G q c' h_max'

    · -- Then show adding a chip anywhere makes it winnable
      exact helper_maximal_superstable_chip_winnable_exact G q c' h_max'

  -- Now dualize, to get a statement about the reverse orientation
  let O' := O.reverse
  have O'_acyc : is_acyclic G O' := is_acyclic_reverse_of_is_acyclic G O O_acyc

  let M' := ordiv G O'
  let D' := canonical_divisor G - D
  have M'_eq : M' = canonical_divisor G - M := by
    rw [← divisor_reverse_orientation O]
    rw [h_M_O]
    simp

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
