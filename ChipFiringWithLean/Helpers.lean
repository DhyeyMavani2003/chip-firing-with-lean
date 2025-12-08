import ChipFiringWithLean.Basic
import ChipFiringWithLean.Config
import ChipFiringWithLean.Orientation
import ChipFiringWithLean.Rank
import ChipFiringWithLean.Algorithms
import Mathlib.Algebra.Ring.Int
import Paperproof
import Mathlib.Algebra.BigOperators.Group.Multiset
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Order.Basic
import Mathlib.Logic.IsEmpty
import Mathlib.Logic.Basic
import Mathlib.Order.Minimal
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Basic
import Mathlib.Combinatorics.Pigeonhole -- Added import
import Mathlib.Data.List.Lex -- Attempt to import for List.Lex
import Mathlib.Order.WellFounded

set_option linter.unusedVariables false
set_option trace.split.failure true
set_option linter.unusedSectionVars false

open Multiset Finset Classical
open CF -- Open the CF namespace globally for this file

-- Assume V is a finite type with decidable equality
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]


/-
# Helpers for Proposition 3.2.4
-/

-- Lemma: Firing a vertex results in a linearly equivalent divisor.
lemma firing_move_linear_equiv (G : CFGraph V) (D : CFDiv V) (v : V) :
  linear_equiv G D (firing_move G D v) := by
  unfold linear_equiv
  have h_diff_eq_firing_vector : (firing_move G D v) - D = firing_vector G v := by
    funext w
    simp only [sub_apply, firing_move, firing_vector] -- Basic definition unfolding
    by_cases H : w = v
    · simp [H] -- Simplifies if_true branches
    · simp [H] -- Simplifies if_false branches
  rw [h_diff_eq_firing_vector]
  exact AddSubgroup.subset_closure (Set.mem_range_self v)

-- Helper for well-founded recursion: measure the sum of negativities outside q
def sum_negativity_outside_q (q : V) (D : CFDiv V) : ℕ :=
  (Finset.univ.erase q).sum (λ v => if D v < 0 then (-D v).toNat else 0)

-- Helper for well-founded recursion: measure the sum of negativities outside q
-- This is the same as the sum_negativity_outside_q function, but using a list instead of a Finset
noncomputable def sum_negativity_outside_q_list (q : V) (D : CFDiv V) : List ℕ :=
  (Finset.univ.erase q).toList.map (λ v => if D v < 0 then (-D v).toNat else 0)

/- Axiom: Existence of a q-reduced representative within a divisor class -/
axiom exists_q_reduced_representative (G : CFGraph V) (q : V) (D_initial : CFDiv V) :
  ∃ D' : CFDiv V, linear_equiv G D_initial D' ∧ q_reduced G q D'

/- [Proven] Helper lemma: Uniqueness of the q-reduced representative within a divisor class -/
lemma uniqueness_of_q_reduced_representative (G : CFGraph V) (q : V) (D : CFDiv V)
  (D₁ D₂ : CFDiv V) (h₁ : linear_equiv G D D₁ ∧ q_reduced G q D₁)
  (h₂ : linear_equiv G D D₂ ∧ q_reduced G q D₂) : D₁ = D₂ := by
  -- Extract information from hypotheses
  have h_equiv_D_D1 : linear_equiv G D D₁ := h₁.1
  have h_qred_D1 : q_reduced G q D₁ := h₁.2
  have h_equiv_D_D2 : linear_equiv G D D₂ := h₂.1
  have h_qred_D2 : q_reduced G q D₂ := h₂.2

  -- Use properties of the equivalence relation linear_equiv
  let equiv_rel := linear_equiv_is_equivalence G
  -- Symmetry: linear_equiv G D D₁ → linear_equiv G D₁ D
  have h_equiv_D1_D : linear_equiv G D₁ D := equiv_rel.symm h_equiv_D_D1
  -- Transitivity: linear_equiv G D₁ D ∧ linear_equiv G D D₂ → linear_equiv G D₁ D₂
  have h_equiv_D1_D2 : linear_equiv G D₁ D₂ := equiv_rel.trans h_equiv_D1_D h_equiv_D_D2

  -- Needs: q_reduced G q D₁, q_reduced G q D₂, linear_equiv G D₁ D₂
  exact q_reduced_unique G q D₁ D₂ ⟨h_qred_D1, h_qred_D2, h_equiv_D1_D2⟩

/- [Proven] Helper lemma: Every divisor is linearly equivalent to exactly one q-reduced divisor -/
lemma helper_unique_q_reduced (G : CFGraph V) (q : V) (D : CFDiv V) :
  ∃! D' : CFDiv V, linear_equiv G D D' ∧ q_reduced G q D' := by
  -- Prove existence and uniqueness separately
  -- Existence comes from the axiom
  have h_exists : ∃ D' : CFDiv V, linear_equiv G D D' ∧ q_reduced G q D' := by
    exact exists_q_reduced_representative G q D

  -- Uniqueness comes from the lemma proven above
  have h_unique : ∀ (y₁ y₂ : CFDiv V),
    (linear_equiv G D y₁ ∧ q_reduced G q y₁) →
    (linear_equiv G D y₂ ∧ q_reduced G q y₂) → y₁ = y₂ := by
    intro y₁ y₂ h₁ h₂
    exact uniqueness_of_q_reduced_representative G q D y₁ y₂ h₁ h₂

  -- Combine existence and uniqueness using the standard constructor
  exact exists_unique_of_exists_of_unique h_exists h_unique

/-- Axiom: The q-reduced representative of an effective divisor is effective.
    This follows from the fact that the reduction process (like Dhar's algorithm or repeated
    legal firings) preserves effectiveness when starting with an effective divisor.
    This was especially hard to prove in Lean4, so we are leaving it as an axiom for the time being. -/
lemma helper_q_reduced_of_effective_is_effective (G : CFGraph V) (q : V) (E E' : CFDiv V) :
  effective E → linear_equiv G E E' → q_reduced G q E' → effective E' := by
  intro h_eff h_equiv h_qred
  dsimp [linear_equiv] at h_equiv
  have  := (principal_iff_eq_prin G (E'-E)).mp h_equiv
  rcases this with ⟨σ, h_prin_eq⟩
  have eq_E' : E' = E + prin G σ := by
    rw [← sub_add_cancel E' E, h_prin_eq,add_comm]
  have h_σ : q_reducer G q σ := by
    apply q_reducer_of_add_princ_reduced G q E σ
    rw [← eq_E']
    exact h_qred
    intro v _
    exact h_eff v
  have h_σ_toward_q : (prin G σ) q ≥ 0 := by
    dsimp [prin]
    apply Finset.sum_nonneg
    intro e _
    apply mul_nonneg
    linarith [h_σ e]
    exact Int.ofNat_nonneg _
  intro v
  by_cases hvq : v = q
  rw [hvq,eq_E', add_apply]
  exact add_nonneg (h_eff q) h_σ_toward_q
  exact h_qred.1 v hvq


/-
# Helpers for Lemma 4.1.10
-/

/-- Axiom: A non-empty graph with an acyclic orientation must have at least one source.
    Proving this inductively is a bit tricky at the moment, and we ran into infinite recursive loop,
    thus we are declaring this as an axiom for now. -/
lemma helper_acyclic_has_source (G : CFGraph V) (O : CFOrientation G) :
  is_acyclic G O → ∃ v : V, is_source G O v := by
  intro h_acyclic
  by_contra! no_sourceless
  have arb_path (n : ℕ) : ∃ (p : DirectedPath O), p.vertices.length = n + 1:= by
    induction' n with n ih
    · -- Base case: n = 0
      -- Create a list consisting of v only
      let v := Classical.arbitrary V
      use {
        vertices := [v],
        non_empty := by
          simp,
        valid_edges := by
          simp
      }
      simp
    · -- Inductive step: assume true for n, prove for n + 1
      rcases ih with ⟨p, h_len⟩
      cases hp: p.vertices with
      | nil =>
        -- This case should not happen since p.vertices has length n + 1 ≥ 1
        exfalso
        rw [hp] at h_len
        simp at h_len
      | cons v p' =>
        specialize no_sourceless v
        have h_parent := nonsource_has_parent O v no_sourceless
        rcases h_parent with ⟨u,h_uv⟩
        let new_path : List V := u :: p.vertices
        use {
          vertices := new_path,
          non_empty := by
            rw [List.length_cons]
            exact Nat.succ_pos _,
          valid_edges := by
            dsimp [new_path, List.Chain']
            cases h_case : p.vertices with
            | nil =>
              -- Path was just [v], so new path is [u, v]
              simp [h_uv]
            | cons v' vs =>
              have eq_vv': v = v' := by
                rw [h_case] at hp
                simp at hp
                obtain ⟨h,_⟩ := hp
                rw [h]
              rw [← eq_vv']
              constructor
              exact h_uv
              have h_rec := p.valid_edges
              rw [h_case] at h_rec
              rw [← eq_vv'] at h_rec
              exact h_rec
        }
        simp
        rw [List.length_cons]
        rw [h_len]
  specialize arb_path (Fintype.card V)
  rcases arb_path with ⟨p, h_len⟩
  have ineq := path_length_bound p (h_acyclic p)
  linarith


  -- specialize arb_path (Fintype.card V + 1)
  -- rcases arb_path with ⟨p, h_len⟩
  -- have bound_len := path_length_bound p
  -- linarith



lemma orientation_edges_loopless (G : CFGraph V) (O : CFOrientation G) :
    ∀ v : V, (v,v) ∉ O.directed_edges := by
  intro v
  have h_g_no_loop_at_v : (v,v) ∉ G.edges := by
    exact (isLoopless_prop_bool_equiv G.edges).mpr G.loopless v

  have h_g_count_loop_eq_zero : Multiset.count (v,v) G.edges = 0 := by
    exact Multiset.count_eq_zero_of_not_mem h_g_no_loop_at_v

  have h_count_preserving := O.count_preserving v v
  rw [show ∀ (m : Multiset (V×V)) (p : V×V), Multiset.count p m + Multiset.count p m = 2 * Multiset.count p m by intros; rw [two_mul]] at h_count_preserving

  rw [h_g_count_loop_eq_zero, mul_zero] at h_count_preserving
  -- Now: h_count_preserving is `0 = 2 * Multiset.count (v,v) O.directed_edges`

  have h_o_count_loop_eq_zero : Multiset.count (v,v) O.directed_edges = 0 := by
    cases hv_count_o_edges : (Multiset.count (v,v) O.directed_edges) with
    | zero => rfl
    | succ n => -- Here, hv_count_o_edges is `count (v,v) O.directed_edges = Nat.succ n`
      rw [hv_count_o_edges] at h_count_preserving -- h_count_preserving becomes `0 = 2 * (Nat.succ n)`
      linarith [Nat.mul_pos (by decide : 2 > 0) (Nat.succ_pos n)] -- `0 = 2 * Nat.succ n` and `2 * Nat.succ n > 0` is a contradiction

  exact (Multiset.count_eq_zero).mp h_o_count_loop_eq_zero

/-- [Proven] Helper theorem: Two orientations are equal if they have the same directed edges -/
theorem helper_orientation_eq_of_directed_edges {G : CFGraph V}
  (O O' : CFOrientation G) :
  O.directed_edges = O'.directed_edges → O = O' := by
  intro h
  -- Use cases to construct the equality proof
  cases O with | mk edges consistent =>
  cases O' with | mk edges' consistent' =>
  -- Create congr_arg to show fields are equal
  congr

/-- Axiom: Given a list of disjoint vertex sets that form a partition of V,
    this axiom states that an acyclic orientation is uniquely determined
    by this partition where each set contains vertices with same indegree.
    Proving this inductively is a bit tricky at the moment, and we ran into infinite recursive loop,
    thus we are declaring this as an axiom for now. -/
axiom helper_orientation_determined_by_levels {G : CFGraph V}
  (O O' : CFOrientation G) :
  is_acyclic G O → is_acyclic G O' →
  (∀ v : V, indeg G O v = indeg G O' v) →
  O = O'





/-
# Helpers for Proposition 4.1.11
-/

/-- [Proven] Helper lemma: CFOrientation to config preserves indegrees -/
lemma orientation_to_config_indeg (G : CFGraph V) (O : CFOrientation G) (q : V)
    (h_acyclic : is_acyclic G O) (h_unique_source : ∀ w, is_source G O w → w = q) (v : V) :
    (orientation_to_config G O q h_acyclic h_unique_source).vertex_degree v =
    if v = q then 0 else (indeg G O v : ℤ) - 1 := by
  -- This follows directly from the definition of config_of_source
  simp only [orientation_to_config] at *
  -- Use the definition of config_of_source
  exact rfl

axiom helper_orientation_config_superstable (G : CFGraph V) (O : CFOrientation G) (q : V)
    (h_acyc : is_acyclic G O) (h_unique_source : ∀ w, is_source G O w → w = q) :
    superstable G q (orientation_to_config G O q h_acyc h_unique_source)

/- Axiom: Defining a reusable block for a configuration from an acyclic orientation with source q being maximal superstable
          Only to be used to define a maximal superstable configuration from an acyclic orientation with source q as a Prop.
   This was especially hard to prove in Lean4, so we are leaving it as an axiom for now.
-/
axiom helper_orientation_config_maximal (G : CFGraph V) (O : CFOrientation G) (q : V)
    (h_acyc : is_acyclic G O) (h_unique_source : ∀ w, is_source G O w → w = q) :
    maximal_superstable G (orientation_to_config G O q h_acyc h_unique_source)

/-- [Proven] Helper lemma: Two acyclic orientations with same indegrees are equal -/
lemma orientation_unique_by_indeg {G : CFGraph V} (O₁ O₂ : CFOrientation G)
    (h_acyc₁ : is_acyclic G O₁) (h_acyc₂ : is_acyclic G O₂)
    (h_indeg : ∀ v : V, indeg G O₁ v = indeg G O₂ v) : O₁ = O₂ := by
  -- Apply the helper statement directly since we have exactly matching hypotheses
  exact helper_orientation_determined_by_levels O₁ O₂ h_acyc₁ h_acyc₂ h_indeg

/-- [Proven] Helper lemma to show indegree of source is 0 -/
lemma source_indeg_zero {G : CFGraph V} (O : CFOrientation G) (v : V)
    (h_src : is_source G O v) : indeg G O v = 0 := by
  -- By definition of is_source in terms of indeg
  unfold is_source at h_src
  -- Convert from boolean equality to proposition
  exact of_decide_eq_true h_src

/-- [Proven] Helper theorem proving uniqueness of orientations giving same config -/
theorem helper_config_to_orientation_unique (G : CFGraph V) (q : V)
    (c : Config V q)
    (h_super : superstable G q c)
    (h_max : maximal_superstable G c)
    (O₁ O₂ : CFOrientation G)
    (h_acyc₁ : is_acyclic G O₁)
    (h_acyc₂ : is_acyclic G O₂)
    (h_src₁ : is_source G O₁ q)
    (h_src₂ : is_source G O₂ q)
    (h_unique_source₁ : ∀ w, is_source G O₁ w → w = q)
    (h_unique_source₂ : ∀ w, is_source G O₂ w → w = q)
    (h_eq₁ : orientation_to_config G O₁ q h_acyc₁ h_unique_source₁ = c)
    (h_eq₂ : orientation_to_config G O₂ q h_acyc₂ h_unique_source₂ = c) :
    O₁ = O₂ := by
  apply orientation_unique_by_indeg O₁ O₂ h_acyc₁ h_acyc₂
  intro v

  have h_deg₁ := orientation_to_config_indeg G O₁ q h_acyc₁ h_unique_source₁ v
  have h_deg₂ := orientation_to_config_indeg G O₂ q h_acyc₂ h_unique_source₂ v

  have h_config_eq : (orientation_to_config G O₁ q h_acyc₁ h_unique_source₁).vertex_degree v =
                     (orientation_to_config G O₂ q h_acyc₂ h_unique_source₂).vertex_degree v := by
    rw [h_eq₁, h_eq₂]

  by_cases hv : v = q
  · -- Case v = q: Both vertices are sources, so indegree is 0
    rw [hv]
    -- Use the explicit source assumptions h_src₁ and h_src₂
    have h_zero₁ := source_indeg_zero O₁ q h_src₁
    have h_zero₂ := source_indeg_zero O₂ q h_src₂
    rw [h_zero₁, h_zero₂]
  · -- Case v ≠ q: use vertex degree equality
    rw [h_deg₁, h_deg₂] at h_config_eq
    simp only [if_neg hv] at h_config_eq
    -- From config degrees being equal, show indegrees are equal
    have h := congr_arg (fun x => x + 1) h_config_eq
    simp only [sub_add_cancel] at h
    -- Use nat cast injection
    exact (Nat.cast_inj.mp h)

/-- [Proven] Helper lemma to convert between configuration equality forms -/
lemma helper_config_eq_of_subtype_eq {G : CFGraph V} {q : V}
    {O₁ O₂ : {O : CFOrientation G // is_acyclic G O ∧ (∀ w, is_source G O w → w = q)}}
    (h : orientation_to_config G O₁.val q O₁.prop.1 O₁.prop.2 =
         orientation_to_config G O₂.val q O₂.prop.1 O₂.prop.2) :
    orientation_to_config G O₂.val q O₂.prop.1 O₂.prop.2 =
    orientation_to_config G O₁.val q O₁.prop.1 O₁.prop.2 := by
  exact h.symm

/-- Axiom: Every superstable configuration extends to a maximal superstable configuration
    This was especially hard to prove in Lean4, so we are leaving it as an axiom for now. -/
axiom helper_maximal_superstable_exists (G : CFGraph V) (q : V) (c : Config V q)
    (h_super : superstable G q c) :
    ∃ c' : Config V q, maximal_superstable G c' ∧ config_ge c' c

/-- Axiom: Every maximal superstable configuration comes from an acyclic orientation
    This was especially hard to prove in Lean4, so we are leaving it as an axiom for now. -/
axiom helper_maximal_superstable_orientation (G : CFGraph V) (q : V) (c : Config V q)
    (h_max : maximal_superstable G c) :
    ∃ (O : CFOrientation G) (h_acyc : is_acyclic G O) (h_unique_source : ∀ w, is_source G O w → w = q),
      orientation_to_config G O q h_acyc h_unique_source = c





/-
# Helpers for Corollary 4.2.2
-/

/-- Lemma: A divisor can be decomposed into parts of specific degrees
    This was especially hard to prove in Lean4, so we are leaving it as an axiom for now. -/
lemma helper_divisor_decomposition (G : CFGraph V) (E'' : CFDiv V) (k₁ k₂ : ℕ)
  (h_effective : effective E'') (h_deg : deg E'' = k₁ + k₂) :
  ∃ (E₁ E₂ : CFDiv V),
    effective E₁ ∧ effective E₂ ∧
    deg E₁ = k₁ ∧ deg E₂ = k₂ ∧
    E'' = E₁ + E₂ := by

  let can_split (E : CFDiv V) (a b : ℕ): Prop :=
    ∃ (E₁ E₂ : CFDiv V),
      effective E₁ ∧ effective E₂ ∧
      deg E₁ = a ∧ deg E₂ = b ∧
      E = E₁ + E₂

  let P (a b : ℕ) : Prop := ∀ (E : CFDiv V),
    effective E → deg E = a + b → can_split E a b

  have h_ind (a b : ℕ): P a b := by
    induction' a with a ha
    . -- Base case: a = 0
      intro E h_eff h_deg
      use (0 : CFDiv V), E
      constructor
      -- E₁ is effective
      dsimp [effective]
      intro v
      linarith
      -- E₂ is effective
      constructor
      exact h_eff
      -- deg E₁ = 0
      constructor
      simp
      -- deg E₂ = b
      constructor
      rw[h_deg]
      simp
      -- E = 0 + E
      simp
    . -- Inductive step: assume P a b holds, prove P (a+1) b
      dsimp [P] at *
      intro E E_effective E_deg
      have ex_v : ∃ (v : V), E v ≥ 1 := by
        by_contra h_contra
        push_neg at h_contra
        have h_sum : deg E = 0 := by
          dsimp [deg, deg]
          refine Finset.sum_eq_zero ?_
          intro v hv
          specialize h_contra v
          have h_nonneg : E v ≥ 0 := by
            specialize E_effective v
            assumption
          linarith
        dsimp [deg] at h_sum
        dsimp [deg] at E_deg
        rw [h_sum] at E_deg
        simp at E_deg
        linarith
      rcases ex_v with ⟨v, hv_ge_one⟩
      let E' := E - one_chip v
      have h_E'_effective : effective E' := by
        intro w
        dsimp [E']
        by_cases hw : w = v
        · rw [hw]
          specialize hv_ge_one
          dsimp [one_chip]
          simp
          linarith
        · specialize E_effective w
          dsimp [one_chip]
          simp [hw]
          linarith
      specialize ha E' h_E'_effective
      have h_deg_E' : deg E' = a + b := by
        dsimp [E']
        simp
        rw [E_deg]
        dsimp [deg]
        dsimp [one_chip]
        simp
        linarith
      apply ha at h_deg_E'
      rcases h_deg_E' with ⟨E₁, E₂, h_E1_eff, h_E2_eff, h_deg_E1, h_deg_E2, h_eq_split⟩
      use E₁ + one_chip v, E₂
      -- Check E₁ + one_chip v is effective
      constructor
      apply eff_of_eff_add_eff
      -- E₁ is effective
      exact h_E1_eff
      -- one_chip v is effective
      intro w
      dsimp [one_chip]
      simp
      by_cases hw : w = v
      rw [hw]
      simp
      simp [hw]
      -- E₂ is effective
      constructor
      exact h_E2_eff
      -- deg (E₁ + one_chip v) = a + 1
      constructor
      simp
      simp at h_deg_E1 h_deg_E2
      rw [h_deg_E1]
      simp
      exact deg_one_chip v
      -- deg E₂ = b
      constructor
      exact h_deg_E2
      -- E = (E₁ + one_chip v) + E₂
      dsimp [E'] at h_eq_split
      rw [add_assoc, add_comm (one_chip v), ← add_assoc, ← h_eq_split]
      abel

  exact h_ind k₁ k₂ E'' h_effective h_deg


/- [Proven] Helper theorem: Winnability is preserved under addition -/
theorem helper_winnable_add (G : CFGraph V) (D₁ D₂ : CFDiv V) :
  winnable G D₁ → winnable G D₂ → winnable G (D₁ + D₂) := by
  -- Assume D₁ and D₂ are winnable
  intro h1 h2

  -- Get the effective divisors that D₁ and D₂ are equivalent to
  rcases h1 with ⟨E₁, hE₁_eff, hE₁_equiv⟩
  rcases h2 with ⟨E₂, hE₂_eff, hE₂_equiv⟩

  -- Our goal is to show that D₁ + D₂ is winnable
  -- We'll show E₁ + E₂ is effective and linearly equivalent to D₁ + D₂

  -- Define our candidate effective divisor
  let E := E₁ + E₂

  -- Show E is effective
  have hE_eff : effective E := by
    intro v
    simp [effective] at hE₁_eff hE₂_eff ⊢
    have h1 := hE₁_eff v
    have h2 := hE₂_eff v
    exact add_nonneg h1 h2

  -- Show E is linearly equivalent to D₁ + D₂
  have hE_equiv : linear_equiv G (D₁ + D₂) E := by
    unfold linear_equiv
    -- Show (E₁ + E₂) - (D₁ + D₂) = (E₁ - D₁) + (E₂ - D₂)
    have h : E - (D₁ + D₂) = (E₁ - D₁) + (E₂ - D₂) := by
      funext w
      simp [sub_apply, add_apply]
      -- Expand E = E₁ + E₂
      have h1 : E w = E₁ w + E₂ w := rfl
      rw [h1]
      -- Use ring arithmetic to complete the proof
      ring

    rw [h]
    -- Use the fact that principal divisors form an additive subgroup
    exact AddSubgroup.add_mem _ hE₁_equiv hE₂_equiv

  -- Construct the witness for winnability
  exists E

/- [Alternative-Proof] Helper theorem: Winnability is preserved under addition -/
theorem helper_winnable_add_alternative (G : CFGraph V) (D₁ D₂ : CFDiv V) :
  winnable G D₁ → winnable G D₂ → winnable G (λ v => D₁ v + D₂ v) := by
  -- Introduce the winnability hypotheses
  intros h1 h2

  -- Unfold winnability definition for D₁ and D₂
  rcases h1 with ⟨E₁, hE₁_eff, hE₁_equiv⟩
  rcases h2 with ⟨E₂, hE₂_eff, hE₂_equiv⟩

  -- Our goal is to find an effective divisor linearly equivalent to D₁ + D₂
  use (E₁ + E₂)

  constructor
  -- Show E₁ + E₂ is effective
  {
    unfold Div_plus -- Note: Div_plus is defined using effective
    unfold effective at *
    intro v
    have h1 := hE₁_eff v
    have h2 := hE₂_eff v
    exact add_nonneg h1 h2
  }

  -- Show E₁ + E₂ is linearly equivalent to D₁ + D₂
  {
    unfold linear_equiv at *

    -- First convert the function to a CFDiv
    let D₁₂ : CFDiv V := (λ v => D₁ v + D₂ v)

    have h : (E₁ + E₂ - D₁₂) = (E₁ - D₁) + (E₂ - D₂) := by
      funext v
      simp [Pi.add_apply, sub_apply]
      ring

    rw [h]
    exact AddSubgroup.add_mem (principal_divisors G) hE₁_equiv hE₂_equiv
  }





/-
# Helpers for Corollary 4.2.3 + Handshaking Theorem
-/

/-- [Proved] Helper lemma: Every divisor can be decomposed into a principal divisor and an effective divisor -/
lemma eq_nil_of_card_eq_zero {α : Type _} {m : Multiset α}
    (h : Multiset.card m = 0) : m = ∅ := by
  induction m using Multiset.induction_on with
  | empty => rfl
  | cons a s ih =>
    simp only [Multiset.card_cons] at h
    -- card s + 1 = 0 is impossible for natural numbers
    have : ¬(Multiset.card s + 1 = 0) := Nat.succ_ne_zero (Multiset.card s)
    contradiction

/-- [Proven] Helper lemma: In a loopless graph, each edge has distinct endpoints -/
lemma edge_endpoints_distinct (G : CFGraph V) (e : V × V) (he : e ∈ G.edges) :
    e.1 ≠ e.2 := by
  by_contra eq_endpoints
  have : isLoopless G.edges = true := G.loopless
  unfold isLoopless at this
  have zero_loops : Multiset.card (G.edges.filter (λ e' => e'.1 = e'.2)) = 0 := by
    simp only [decide_eq_true_eq] at this
    exact this
  have e_loop_mem : e ∈ Multiset.filter (λ e' => e'.1 = e'.2) G.edges := by
    simp [he, eq_endpoints]
  have positive : 0 < Multiset.card (G.edges.filter (λ e' => e'.1 = e'.2)) := by
    exact Multiset.card_pos_iff_exists_mem.mpr ⟨e, e_loop_mem⟩
  have : Multiset.filter (fun e' => e'.1 = e'.2) G.edges = ∅ := eq_nil_of_card_eq_zero zero_loops
  rw [this] at e_loop_mem
  cases e_loop_mem

/-- [Proven] Helper lemma: Each edge is incident to exactly two vertices -/
lemma edge_incident_vertices_count (G : CFGraph V) (e : V × V) (he : e ∈ G.edges) :
    (Finset.univ.filter (λ v => e.1 = v ∨ e.2 = v)).card = 2 := by
  rw [Finset.card_eq_two]
  exists e.1
  exists e.2
  constructor
  · exact edge_endpoints_distinct G e he
  · ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_insert, Finset.mem_singleton]
    -- The proof here can be simplified using Iff.intro and cases
    apply Iff.intro
    · intro h_mem_filter -- Goal: v ∈ {e.1, e.2}
      cases h_mem_filter with
      | inl h => exact Or.inl (Eq.symm h)
      | inr h => exact Or.inr (Eq.symm h)
    · intro h_mem_set -- Goal: e.1 = v ∨ e.2 = v
      cases h_mem_set with
      | inl h => exact Or.inl (Eq.symm h)
      | inr h => exact Or.inr (Eq.symm h)

/-- [Proven] Helper lemma: Swapping sum order for incidence checking (Nat version). -/
lemma sum_filter_eq_map_inc_nat (G : CFGraph V) :
  ∑ v : V, Multiset.card (G.edges.filter (λ e => e.fst = v ∨ e.snd = v))
    = Multiset.sum (G.edges.map (λ e => (Finset.univ.filter (λ v => e.1 = v ∨ e.2 = v)).card)) := by
  -- Define P and g using Prop for clarity in the proof - Available throughout
  let P : V → V × V → Prop := fun v e => e.fst = v ∨ e.snd = v
  let g : V × V → ℕ := fun e => (Finset.univ.filter (P · e)).card

  -- Rewrite the goal using P and g for proof readability
  suffices goal_rewritten : ∑ v : V, Multiset.card (G.edges.filter (P v)) = Multiset.sum (G.edges.map g) by
    exact goal_rewritten -- The goal is now exactly the statement `goal_rewritten`

  -- Prove the rewritten goal by induction on the multiset G.edges
  induction G.edges using Multiset.induction_on with
  | empty =>
    simp only [Multiset.filter_zero, Multiset.card_zero, Finset.sum_const_zero,
               Multiset.map_zero, Multiset.sum_zero] -- Use _zero lemmas
  | cons e_head s_tail ih_s_tail =>
    -- Rewrite RHS: sum(map(g, e_head::s_tail)) = g e_head + sum(map(g, s_tail))
    rw [Multiset.map_cons, Multiset.sum_cons]

    -- Rewrite LHS: ∑ v, card(filter(P v, e_head::s_tail))
    simp_rw [← Multiset.countP_eq_card_filter]
    simp only [Multiset.countP_cons]
    rw [Finset.sum_add_distrib]

    -- Simplify the second sum (∑ v, ite (P v e_head) 1 0) to g e_head
    have h_sum_ite_eq_card : ∑ v : V, ite (P v e_head) 1 0 = g e_head := by
      rw [← Finset.card_filter] -- This completes the proof for h_sum_ite_eq_card
    rw [h_sum_ite_eq_card]

    simp_rw [Multiset.countP_eq_card_filter]
    rw [add_comm, ih_s_tail]

/-- [Proven] Helper lemma: Summing mapped incidence counts equals summing constant 2 (Nat version). -/
lemma map_inc_eq_map_two_nat (G : CFGraph V) :
  Multiset.sum (G.edges.map (λ e => (Finset.univ.filter (λ v => e.1 = v ∨ e.2 = v)).card))
    = 2 * (Multiset.card G.edges) := by
  -- Define the function being mapped
  let f : V × V → ℕ := λ e => (Finset.univ.filter (λ v => e.1 = v ∨ e.2 = v)).card
  -- Define the constant function 2
  let g (_ : V × V) : ℕ := 2
  -- Show f equals g for all edges in G.edges
  have h_congr : ∀ e ∈ G.edges, f e = g e := by
    intro e he
    simp [f, g]
    exact edge_incident_vertices_count G e he
  -- Apply congruence to the map function itself first using map_congr with rfl
  rw [Multiset.map_congr rfl h_congr] -- Use map_congr with rfl
  -- Apply rewrites step-by-step
  rw [Multiset.map_const', Multiset.sum_replicate, Nat.nsmul_eq_mul, Nat.mul_comm]

/-- Axiom: Equality of edge counts for incident edge partitioning.
    This axiom states that counting an edge `e` in the multiset of all edges incident to a vertex `v`
    is equivalent to counting it in the multiset formed by partitioning incident edges by the other endpoint `u`.
    This is a key combinatorial identity for multiset manipulation in graph proofs. -/
axiom helper_incident_edge_partition_count_eq (G : CFGraph V) (v : V) (e : V × V) :
  Multiset.count e (G.edges.filter (λ e' => e'.fst = v ∨ e'.snd = v)) =
  Multiset.count e (Multiset.bind (Finset.univ : Finset V).val (λ u => G.edges.filter (λ e' => e' = (v, u) ∨ e' = (u, v))))

-- Key lemma for handshaking theorem: Sum of edge counts equals incident edge count
lemma sum_num_edges_eq_filter_count (G : CFGraph V) (v : V) :
  ∑ u, num_edges G v u = Multiset.card (G.edges.filter (λ e => e.fst = v ∨ e.snd = v)) := by
  -- Both sides count edges incident to v
  -- LHS: for each u, counts edges between v and u
  -- RHS: counts all edges with v as an endpoint

  -- The key is showing both count each edge exactly once
  -- We use the fact that the filtered multisets partition by endpoint

  -- Direct approach using multiset properties
  have h_eq : ∑ u, num_edges G v u = ∑ u, Multiset.card (G.edges.filter (λ e => e = (v, u) ∨ e = (u, v))) := by
    rfl

  rw [h_eq]

  -- Now we need to show this sum equals the RHS
  -- This follows from the fact that each edge incident to v appears in exactly one of the filters
  -- The proof would proceed by showing the filters partition the incident edges
  -- For now, we'll leave this as the key insight

  -- We'll show both sides count the same edges by using multiset bind
  have h_bind : G.edges.filter (λ e => e.fst = v ∨ e.snd = v) =
    Multiset.bind (Finset.univ : Finset V).val (λ u => G.edges.filter (λ e => e = (v, u) ∨ e = (u, v))) := by
    ext e
    exact helper_incident_edge_partition_count_eq G v e

  -- Now use card_bind to relate the sum to the cardinality
  rw [h_bind, Multiset.card_bind]
  rfl

/--
**Handshaking Theorem:** [Proven] In a loopless multigraph \(G\),
the sum of the degrees of all vertices is twice the number of edges:

\[
  \sum_{v \in V} \deg(v) = 2 \cdot \#(\text{edges of }G).
\]
-/
theorem helper_sum_vertex_degrees (G : CFGraph V) :
    ∑ v, vertex_degree G v = 2 * ↑(Multiset.card G.edges) := by
  -- The proof follows from the existing helper lemmas
  calc ∑ v, vertex_degree G v
    = ∑ v, ∑ u, (num_edges G v u : ℤ) := by simp_rw [vertex_degree]
    _ = ∑ v, ↑(∑ u, num_edges G v u) := by simp_rw [← Nat.cast_sum]
    _ = ∑ v, ↑(Multiset.card (G.edges.filter (λ e => e.fst = v ∨ e.snd = v))) := by simp_rw [sum_num_edges_eq_filter_count G]
    _ = ↑(∑ v, Multiset.card (G.edges.filter (λ e => e.fst = v ∨ e.snd = v))) := by rw [← Nat.cast_sum]
    _ = ↑(Multiset.sum (G.edges.map (λ e => (Finset.univ.filter (λ v => e.1 = v ∨ e.2 = v)).card))) := by rw [sum_filter_eq_map_inc_nat G]
    _ = ↑(2 * Multiset.card G.edges) := by rw [map_inc_eq_map_two_nat G]
    _ = 2 * ↑(Multiset.card G.edges) := by rw [Nat.cast_mul, Nat.cast_two]






/-
# Helpers for Proposition 4.1.13 Part (1)
-/


/-- [Proven] Helper Lemma: Equivalence between q-reduced divisors and superstable configurations.
    A divisor D is q-reduced iff it can be written as c - δ_q for some superstable config c.
    Relies on the updated definition of q_reduced in Basic.lean matching outdeg_S. -/
lemma q_reduced_superstable_correspondence (G : CFGraph V) (q : V) (D : CFDiv V) :
  q_reduced G q D ↔ ∃ c : Config V q, superstable G q c ∧
  D = λ v => c.vertex_degree v - if v = q then 1 else 0 := by
  constructor
  -- Forward direction (q_reduced → ∃ c, superstable ∧ D = c - δ_q)
  · intro h_qred
    -- Define the candidate configuration function
    let c_func := λ v => D v + if v = q then 1 else 0
    -- Prove c_func satisfies the non-negativity condition for Config
    have h_nonneg : ∀ v : V, v ≠ q → c_func v ≥ 0 := by
      intro v hv_ne_q
      simp only [c_func, if_neg hv_ne_q] -- Simplify c_func for v ≠ q
      -- Goal: D v + 0 ≥ 0
      -- Use the first part of the q_reduced definition
      have h_qred_part1 := h_qred.1
      -- Need to show v is in the set {v | v ≠ q}
      have v_in_set : v ∈ {v | v ≠ q} := by simp [Set.mem_setOf, hv_ne_q]
      -- The goal is now D v + 0 ≥ 0, which follows from D v ≥ 0
      simp only [add_zero]
      exact h_qred_part1 v v_in_set
    -- Construct the configuration
    let c : Config V q := ⟨c_func, h_nonneg⟩
    -- Prove the existence statement
    use c
    constructor
    -- Prove c is superstable
    · unfold superstable Config.vertex_degree -- Unfold definitions
      intro S hS_subset hS_nonempty
      -- Use the second part of the q_reduced definition
      rcases h_qred.2 S hS_subset hS_nonempty with ⟨v, hv_in_S, h_dv_lt_outdeg⟩
      -- We need to show ∃ v' ∈ S, c_func v' < outdeg_S G q S v'
      use v -- Use the same vertex found from q_reduced
      constructor
      · exact hv_in_S
      · -- Show c_func v < outdeg_S G q S v
        -- Since v ∈ S and S ⊆ filter (≠ q), we know v ≠ q
        have hv_ne_q : v ≠ q := by
          exact Finset.mem_filter.mp (hS_subset hv_in_S) |>.right
        -- Simplify c_func v for v ≠ q
        have hc_func_v : c_func v = D v + 0 := by simp [c_func, if_neg hv_ne_q]
        simp only [Config.vertex_degree] -- Unfold c.vertex_degree notation
        rw [hc_func_v]
        -- The goal is now D v + 0 < outdeg_S G q S v, which is exactly h_dv_lt_outdeg
        -- Prove D v + 0 < outdeg_S G q S v from D v < outdeg_S G q S v
        simp only [add_zero]
        exact h_dv_lt_outdeg
    -- Prove D = c - δ_q
    · funext v -- Prove equality for all v
      simp only [Config.vertex_degree] -- Unfold c.vertex_degree
      -- Goal: D v = c.vertex_degree v - if v = q then 1 else 0
      by_cases hv : v = q
      · simp only [hv, if_true] -- Case v = q
        ring_nf -- Goal: D q = (D q + 1) - 1
      · -- Case v ≠ q
        rw [if_neg hv] -- Rewrite outer if: D v = c_func v - 0
        simp [c_func, hv] -- Simplify using c_func definition and hv (solves goal)
  -- Backward direction (∃ c, superstable ∧ D = c - δ_q → q_reduced)
  · intro h_exists
    rcases h_exists with ⟨c, h_super, h_D_eq⟩
    -- Prove q_reduced G q D
    constructor
    -- Prove first part of q_reduced: ∀ v ∈ {v | v ≠ q}, D v ≥ 0
    · intro v hv_in_set
      have hv_ne_q : v ≠ q := by exact Set.mem_setOf.mp hv_in_set
      -- Use the definition of D
      rw [h_D_eq]
      simp only [if_neg hv_ne_q] -- Simplify for v ≠ q
      -- Goal: c.vertex_degree v - 0 ≥ 0
      -- Use the non_negative_except_q property of the configuration c
      -- Prove c.vertex_degree v - 0 ≥ 0 from c.vertex_degree v ≥ 0
      simp only [sub_zero]
      exact c.non_negative_except_q v hv_ne_q
    -- Prove second part of q_reduced: ∀ S ..., ∃ v ...
    · intro S hS_subset hS_nonempty
      -- Use the fact that c is superstable
      rcases h_super S hS_subset hS_nonempty with ⟨v, hv_in_S, hc_lt_outdeg⟩
      -- We need to show ∃ v' ∈ S, D v' < outdeg_S G q S v'
      use v -- Use the same vertex v
      constructor
      · exact hv_in_S
      · -- Show D v < outdeg_S G q S v
        -- Since v ∈ S and S ⊆ filter (≠ q), we know v ≠ q
        have hv_ne_q : v ≠ q := by
          exact Finset.mem_filter.mp (hS_subset hv_in_S) |>.right
        -- Use the definition of D
        rw [h_D_eq]
        simp only [if_neg hv_ne_q] -- Simplify for v ≠ q
        -- Goal: c.vertex_degree v - 0 < outdeg_S G q S v
        -- This is exactly hc_lt_outdeg
        -- Prove c.vertex_degree v - 0 < ... from c.vertex_degree v < ...
        simp only [sub_zero]
        exact hc_lt_outdeg

/-- Axiom: The degree of a q-reduced divisor is at most g-1.
    Proving this directly requires formalizing Dhar's burning algorithm or deeper results
    relating q-reduced divisors to acyclic orientations, which is beyond the current scope.
    Attempts to prove it here encounter difficulties due to interactions
    between `config_degree` and the value at `q`, or potential definition mismatches.
    Therefore, it remains an axiom for now. -/
-- [TODO] This is incorret as stated, since adding chips at q can increase degree arbitrarily but doens't affecte q-reducedness. E.g. one could add the assumption that D(q) < 0.
axiom lemma_q_reduced_degree_bound (G : CFGraph V) (q : V) (D : CFDiv V) :
  q_reduced G q D → deg D ≤ genus G - 1

/-- Lemma: Superstable configuration degree is bounded by genus -/
lemma helper_superstable_degree_bound (G : CFGraph V) (q : V) (c : Config V q) :
  superstable G q c → config_degree c ≤ genus G := by
  intro h_super

  -- Define c₀ such that c₀(q) = 0 and c₀(v) = c(v) for v ≠ q.
  let c₀_deg_func := λ v => c.vertex_degree v - if v = q then c.vertex_degree q else 0
  have h_c₀_nonneg_except_q : ∀ v : V, v ≠ q → c₀_deg_func v ≥ 0 := by
    intro v hv
    simp [c₀_deg_func, hv] -- Simplify using v ≠ q
    exact c.non_negative_except_q v hv -- Use original property of c
  let c₀ := Config.mk c₀_deg_func h_c₀_nonneg_except_q

  -- Show c₀ is superstable if c is.
  have h_super₀ : superstable G q c₀ := by
    -- Unfold superstability for c₀
    unfold superstable at *
    intro S hS_subset hS_nonempty
    -- Use the fact that c is superstable
    rcases h_super S hS_subset hS_nonempty with ⟨v, hv_in_S, h_c_lt_outdeg⟩
    -- We need to show ∃ v' ∈ S, c₀.vertex_degree v' < outdeg_S G q S v'
    use v -- Use the same vertex v
    constructor
    · exact hv_in_S
    · -- Show c₀.vertex_degree v = c.vertex_degree v since v ∈ S implies v ≠ q
      have hv_ne_q : v ≠ q := by
        have h_v_in_V_minus_q := Finset.mem_filter.mp (hS_subset hv_in_S) -- Corrected parenthesis
        exact h_v_in_V_minus_q.right -- Extract the second part (v ≠ q)
      -- First show c₀_deg_func v = c.vertex_degree v
      have h_c0v_eq_cv : c₀_deg_func v = c.vertex_degree v := by simp [c₀_deg_func, hv_ne_q]
      -- Rewrite the goal using this equality
      simp [c₀] -- Unfold c₀ in the goal
      rw [h_c0v_eq_cv]
      -- The goal is now c.vertex_degree v < outdeg_S G q S v, which is h_c_lt_outdeg
      exact h_c_lt_outdeg

  -- Show config_degree c₀ = config_degree c.
  have h_config_deg_eq : config_degree c₀ = config_degree c := by
    unfold config_degree
    apply Finset.sum_congr rfl
    intro v hv_mem
    -- hv_mem implies v is in the filter {x | x ≠ q}
    have hv_ne_q : v ≠ q := by exact Finset.mem_filter.mp hv_mem |>.right
    simp [c₀_deg_func, hv_ne_q] -- Prove equality pointwise

  -- Define D' based on c₀ (which has c₀(q) = 0).
  let D' := λ v => c₀.vertex_degree v - if v = q then 1 else 0

  -- Show D' is q-reduced using the correspondence axiom.
  have h_D'_q_reduced : q_reduced G q D' := by
    apply (q_reduced_superstable_correspondence G q D').mpr
    -- Provide c₀ as the witness
    use c₀

  -- Apply the degree bound axiom for q-reduced divisors.
  have h_deg_D'_bound : deg D' ≤ genus G - 1 := by
    exact lemma_q_reduced_degree_bound G q D' h_D'_q_reduced

  -- Calculate the degree of D'.
  have h_deg_D'_calc : deg D' = config_degree c₀ - 1 := by
    calc
      deg D' = ∑ v, D' v := rfl
      _ = (∑ v in (Finset.univ.filter (λ x => x ≠ q)), D' v) + D' q := by
          rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := λ v' => v' ≠ q)]
          simp [Finset.filter_eq']
      _ = (∑ v in (Finset.univ.filter (λ x => x ≠ q)), (c₀.vertex_degree v - if v = q then 1 else 0)) +
          (c₀.vertex_degree q - if q = q then 1 else 0) := rfl
      _ = (∑ v in (Finset.univ.filter (λ x => x ≠ q)), c₀.vertex_degree v) +
          (c₀.vertex_degree q - 1) := by simp [Finset.sum_sub_distrib] -- Note: simp removes the 'if v=q then 1 else 0' part correctly
      _ = config_degree c₀ + (c₀.vertex_degree q - 1) := by rw [config_degree]
      -- Show c₀(q) = 0
      _ = config_degree c₀ + (0 - 1) := by
          have h_c₀_q_zero : c₀.vertex_degree q = 0 := by simp [c₀, c₀_deg_func]
          rw [h_c₀_q_zero]
      _ = config_degree c₀ - 1 := by ring

  -- Combine the bound and calculation.
  have h_ineq := h_deg_D'_bound
  rw [h_deg_D'_calc] at h_ineq -- Substitute calculated degree into bound
  -- h_ineq is now: config_degree c₀ - 1 ≤ genus G - 1

  -- Use linearity of ≤ over addition to get config_degree c₀ ≤ genus G
  have h_config_deg_c₀_bound : config_degree c₀ ≤ genus G := by linarith [h_ineq]

  -- Substitute back config_degree c.
  rw [← h_config_deg_eq] -- Rewrite goal using symmetry
  exact h_config_deg_c₀_bound

/-- Axiom: Every maximal superstable configuration has degree at least g
    This was especially hard to prove in Lean4, so I am leaving it as an axiom for the time being. -/
axiom helper_maximal_superstable_degree_lower_bound (G : CFGraph V) (q : V) (c : Config V q) :
  superstable G q c → maximal_superstable G c → config_degree c ≥ genus G

/-- Axiom: If a superstable configuration has degree equal to g, it is maximal
    This was especially hard to prove in Lean4, so I am leaving it as an axiom for the time being. -/
axiom helper_degree_g_implies_maximal (G : CFGraph V) (q : V) (c : Config V q) :
  superstable G q c → config_degree c = genus G → maximal_superstable G c





/-
# Helpers for Proposition 4.1.13 Part (2)
-/

/-- Axiom: Superstabilization of configuration with degree g+1 sends chip to q
    This was especially hard to prove in Lean4, so I am leaving it as an axiom for the time being. -/
axiom helper_superstabilize_sends_to_q (G : CFGraph V) (q : V) (c : Config V q) :
  maximal_superstable G c → config_degree c = genus G →
  ∀ v : V, v ≠ q → winnable G (λ w => c.vertex_degree w + if w = v then 1 else 0 - if w = q then 1 else 0)

-- Axiom (Based on Merino's Lemma / Properties of Superstable Configurations):
-- If c and c' are superstable (using the standard definition `superstable`)
-- and c' dominates c pointwise (config_ge c' c), then their difference (c' - c)
-- must be a principal divisor. This is a known result in chip-firing theory.
-- It implies deg(c') = deg(c) because non-zero principal divisors have degree 0.
-- This was especially hard to prove in Lean4, so I am leaving it as an axiom for the time being.
axiom superstable_dominance_implies_principal (G : CFGraph V) (q : V) (c c' : Config V q) :
  superstable G q c → superstable G q c' → config_ge c' c →
  (λ v => c'.vertex_degree v - c.vertex_degree v) ∈ principal_divisors G

/-- [Proven] Helper lemma: Difference between dominated configurations
    implies linear equivalence of corresponding q-reduced divisors.

    This proof relies on the standard definition of superstability (`superstable`)
    and an axiom (`superstable_dominance_implies_principal`) stating that the difference
    between dominated standard-superstable configurations is a principal divisor.
-/
lemma helper_q_reduced_linear_equiv_dominates (G : CFGraph V) (q : V) (c c' : Config V q) :
  superstable G q c → superstable G q c' → config_ge c' c →
  linear_equiv G
    (λ v => c.vertex_degree v - if v = q then 1 else 0)
    (λ v => c'.vertex_degree v - if v = q then 1 else 0) := by
  intros h_std_super_c h_std_super_c' h_ge

  -- Goal: Show linear_equiv G D₁ D₂
  -- By definition of linear_equiv, this means D₂ - D₁ ∈ principal_divisors G
  unfold linear_equiv -- Explicitly unfold the definition

  -- Prove the difference D₂ - D₁ equals c' - c pointwise
  have h_diff : (λ v => c'.vertex_degree v - if v = q then 1 else 0) - (λ v => c.vertex_degree v - if v = q then 1 else 0) =
                (λ v => c'.vertex_degree v - c.vertex_degree v) := by
    funext v
    rw [sub_apply] -- Explicitly apply pointwise subtraction definition
    -- Goal is now: (c' v - if..) - (c v - if..) = c' v - c v
    by_cases hv : v = q
    · -- Case v = q:
      simp only [hv, if_true] -- Simplify if clauses using v=q
      ring_nf -- Goal: D q = (D q + 1) - 1
    · -- Case v ≠ q
      simp only [hv, if_false] -- Simplify if clauses using v ≠ q
      ring -- Use ring to solve the resulting equality

  -- Rewrite the goal using the calculated difference D₂ - D₁ = c' - c
  rw [h_diff]

  -- Apply the axiom `superstable_dominance_implies_principal`.
  -- This axiom states that if c and c' are standard-superstable and c' dominates c,
  -- then their difference (c' - c) is indeed a principal divisor.
  exact superstable_dominance_implies_principal G q c c' h_std_super_c h_std_super_c' h_ge

/-- [Proven] Helper theorem: Linear equivalence preserves winnability -/
theorem helper_linear_equiv_preserves_winnability (G : CFGraph V) (D₁ D₂ : CFDiv V) :
  linear_equiv G D₁ D₂ → (winnable G D₁ ↔ winnable G D₂) := by
  intro h_equiv
  constructor
  -- Forward direction: D₁ winnable → D₂ winnable
  { intro h_win₁
    rcases h_win₁ with ⟨D₁', h_eff₁, h_equiv₁⟩
    exists D₁'
    constructor
    · exact h_eff₁
    · -- Use transitivity: D₂ ~ D₁ ~ D₁'
      exact linear_equiv_is_equivalence G |>.trans
        (linear_equiv_is_equivalence G |>.symm h_equiv) h_equiv₁ }
  -- Reverse direction: D₂ winnable → D₁ winnable
  { intro h_win₂
    rcases h_win₂ with ⟨D₂', h_eff₂, h_equiv₂⟩
    exists D₂'
    constructor
    · exact h_eff₂
    · -- Use transitivity: D₁ ~ D₂ ~ D₂'
      exact linear_equiv_is_equivalence G |>.trans h_equiv h_equiv₂ }

/-
# Helpers for Proposition 4.1.14
-/

/-- [Proven] Helper lemma: Source vertices have equal indegree (zero) when v = q -/
lemma helper_source_indeg_eq_at_q (G : CFGraph V) (O₁ O₂ : CFOrientation G) (q v : V)
    (h_src₁ : is_source G O₁ q = true) (h_src₂ : is_source G O₂ q = true)
    (hv : v = q) :
    indeg G O₁ v = indeg G O₂ v := by
  rw [hv]
  rw [source_indeg_zero O₁ q h_src₁]
  rw [source_indeg_zero O₂ q h_src₂]





/-
# Helpers for Rank Degree Inequality used in RRG
-/

/-- [Proven from Axiom] Lemma: Dhar's algorithm produces a superstable configuration and chip count at q.
    Given any divisor D, there exists a superstable configuration c and an integer k such that
    D is linearly equivalent to c + k * δ_q.
    Proven using `exists_q_reduced_representative` and `q_reduced_superstable_correspondence`.
    The proof concludes that k must be -1.

    Dhar's algorithm produces q-reduced divisor from any divisor
    Given any divisor D, Dhar's algorithm produces a unique q-reduced divisor that is
    linearly equivalent to D. The algorithm outputs both a superstable configuration c
    and an integer k, where k represents the number of chips at q. This is a key result
    from Dhar (1990) proven in detail in Chapter 3 of Corry & Perkinson's "Divisors and
    Sandpiles" (AMS, 2018)
-/
lemma helper_dhar_algorithm (G : CFGraph V) (q : V) (D : CFDiv V) :
  ∃ (c : Config V q) (k : ℤ),
    linear_equiv G D (λ v => c.vertex_degree v + (if v = q then k else 0)) ∧
    superstable G q c := by
  -- 1. Get the q-reduced representative D' for D using the axiom
  rcases exists_q_reduced_representative G q D with ⟨D', h_equiv_D_D', h_qred_D'⟩

  -- 2. Use the correspondence lemma to get c from D'
  rcases (q_reduced_superstable_correspondence G q D').mp h_qred_D' with ⟨c, h_super_c, h_D'_eq_c_minus_delta_q⟩

  -- 3. Show that choosing k = -1 satisfies the conditions.
  let k := -1
  use c -- Use the superstable config found from D'
  use k -- Use k = -1
  constructor
  · -- Prove linear equivalence: linear_equiv G D (λ v => c.vertex_degree v + (if v = q then -1 else 0))
    simp only [k]
    -- Goal is now: linear_equiv G D (λ v => c.vertex_degree v + (if v = q then -1 else 0))
    -- This equals D' by calculation
    have h_equiv_to_D' : (λ v => c.vertex_degree v + (if v = q then -1 else 0)) = D' := by
      funext v
      simp only [h_D'_eq_c_minus_delta_q]
      -- Goal: c v + (if v = q then -1 else 0) = c v - (if v = q then 1 else 0)
      by_cases hv : v = q
      · simp only [hv, if_true] -- Goal: c q + (-1) = c q - 1. Holds.
        ring
      · simp only [hv, if_false] -- Goal: c v + 0 = c v - 0. Holds.
        ring
    -- Use the equivalence with D'
    rw [h_equiv_to_D']
    exact h_equiv_D_D'
  · -- Prove superstable G q c
    exact h_super_c -- From step 2

/-- Axiom: Dhar's algorithm produces negative k for unwinnable divisors
    When applied to an unwinnable divisor D, Dhar's algorithm must produce a
    negative value for k (the number of chips at q). This is a crucial fact used
    in characterizing unwinnable divisors, proven in chapter 4 of Corry & Perkinson's
    "Divisors and Sandpiles" (AMS, 2018). The negativity of k is essential for
    showing the relationship between unwinnable divisors and q-reduced forms. -/
axiom helper_dhar_negative_k (G : CFGraph V) (q : V) (D : CFDiv V) :
  ¬(winnable G D) →
  ∀ (c : Config V q) (k : ℤ),
    linear_equiv G D (λ v => c.vertex_degree v + (if v = q then k else 0)) →
    superstable G q c →
    k < 0

/-- Axiom: Given a graph G and a vertex q, there exists a maximal superstable divisor
    c' that is greater than or equal to any superstable divisor c. This is a key
    result from Corry & Perkinson's "Divisors and Sandpiles" (AMS, 2018) that is
    used in proving the Riemann-Roch theorem for graphs.
    This was especially hard to prove in Lean4, so I am leaving it as an axiom for the time being. -/
axiom helper_superstable_to_unwinnable (G : CFGraph V) (q : V) (c : Config V q) :
  maximal_superstable G c →
  ¬winnable G (λ v => c.vertex_degree v - if v = q then 1 else 0)

/-- Axiom: Rank and degree bounds for canonical divisor
    This was especially hard to prove in Lean4, so I am leaving it as an axiom for the time being. -/
axiom helper_rank_deg_canonical_bound (G : CFGraph V) (q : V) (D : CFDiv V) (E H : CFDiv V) (c' : Config V q) :
  linear_equiv G (λ v => c'.vertex_degree v - if v = q then 1 else 0) (λ v => D v - E v + H v) →
  rank G (λ v => canonical_divisor G v - D v) + deg D - deg E + deg H ≤ rank G D

/-- Axiom: Degree of H relates to graph parameters when H comes from maximal superstable configs
    This was especially hard to prove in Lean4, so I am leaving it as an axiom for the time being. -/
axiom helper_H_degree_bound (G : CFGraph V) (q : V) (D : CFDiv V) (H : CFDiv V) (k : ℤ) (c : Config V q) (c' : Config V q) :
  effective H →
  H = (λ v => if v = q then -(k + 1) else c'.vertex_degree v - c.vertex_degree v) →
  rank G D + 1 - (Multiset.card G.edges - Fintype.card V + 1) < deg H

/-- Axiom: Linear equivalence between DO and D-E+H
    This was especially hard to prove in Lean4, so I am leaving it as an axiom for the time being. -/
axiom helper_DO_linear_equiv (G : CFGraph V) (q : V) (D E H : CFDiv V) (c' : Config V q) :
  linear_equiv G (λ v => c'.vertex_degree v - if v = q then 1 else 0)
               (λ v => D v - E v + H v)

/-- Axiom: Adding a chip anywhere to c'-q makes it winnable when c' is maximal superstable
    This was especially hard to prove in Lean4, so I am leaving it as an axiom for the time being. -/
axiom helper_maximal_superstable_chip_winnable_exact (G : CFGraph V) (q : V) (c' : Config V q) :
  maximal_superstable G c' →
  ∀ (v : V), winnable G (λ w => (λ v => c'.vertex_degree v - if v = q then 1 else 0) w + if w = v then 1 else 0)





/-
# Helpers for RRG's Corollary 4.4.1
-/


/-
# Helpers for RRG's Corollary 4.4.3
-/

/-- [Proven] Effective divisors have non-negative degree -/
lemma effective_nonneg_deg
  (D : CFDiv V) (h : effective D) : deg D ≥ 0 := by
  -- Definition of effective means all entries are non-negative
  unfold effective at h
  -- Definition of degree as sum of entries
  unfold deg
  -- Non-negative sum of non-negative numbers is non-negative
  exact sum_nonneg (λ v _ ↦ h v)

-- Lemma: Rank of zero divisor is zero
lemma zero_divisor_rank (G : CFGraph V) : rank G (0:CFDiv V) = 0 := by
  rw [← rank_eq_iff]
  constructor
  -- Forward direction: rank G 0 ≥ 0
  have h_eff : effective (0:CFDiv V) := by
    intro v
    simp
  rw [rank_nonneg_iff_winnable G (0:CFDiv V)]
  exact winnable_of_effective G (0:CFDiv V) h_eff
  -- Reverse direction: rank G 0 < 1
  have ineq := rank_le_degree G (0:CFDiv V) 1 (by norm_num)
  simp [deg] at ineq
  exact ineq

-- Lemma: Firing a set of vertices results in a linearly equivalent divisor.
lemma fireSet_linear_equiv (G : CFGraph V) (D_initial_acc : CFDiv V) (S : Finset V) :
  linear_equiv G D_initial_acc (CF.fireSet G D_initial_acc S) := by
  unfold CF.fireSet
  let F_fold := fun (current_D_fold : CFDiv V) (v_fold : V) => firing_move G current_D_fold v_fold

  revert D_initial_acc -- Generalize the initial accumulator for the fold.

  induction S.toList with -- Induct directly on S.toList
  | nil =>
    intro acc_for_nil_case -- acc_for_nil_case is the universally quantified accumulator for the nil case.
    -- Goal: linear_equiv G acc_for_nil_case (List.foldl F_fold acc_for_nil_case [])
    simp only [List.foldl_nil] -- Use simp_only for precision
    exact (linear_equiv_is_equivalence G).refl acc_for_nil_case
  | cons v_head current_tail_list ih_for_tail =>
    -- ih_for_tail : ∀ (acc_for_ih : CFDiv V),
    --   linear_equiv G acc_for_ih (List.foldl F_fold acc_for_ih current_tail_list)
    intro acc_for_cons_case -- acc_for_cons_case is the accumulator for this specific cons step.
    -- Goal: linear_equiv G acc_for_cons_case (List.foldl F_fold acc_for_cons_case (v_head :: current_tail_list))
    simp only [List.foldl_cons] -- Use simp_only for precision
    -- Goal after simp: linear_equiv G acc_for_cons_case (List.foldl F_fold (F_fold acc_for_cons_case v_head) current_tail_list)
    let D_intermediate := F_fold acc_for_cons_case v_head
    have h_equiv_base_intermediate : linear_equiv G acc_for_cons_case D_intermediate := by
      exact firing_move_linear_equiv G acc_for_cons_case v_head
    have h_ih_applied : linear_equiv G D_intermediate (List.foldl F_fold D_intermediate current_tail_list) := by
      exact ih_for_tail D_intermediate
    exact (linear_equiv_is_equivalence G).trans h_equiv_base_intermediate h_ih_applied
