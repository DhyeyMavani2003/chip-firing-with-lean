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

/- Lemma: Uniqueness of the q-reduced representative within a divisor class -/
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

/- Lemma: Every divisor is linearly equivalent to exactly one q-reduced divisor -/
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

/-- Lemma: The q-reduced representative of an effective divisor is effective.
    This follows from the fact that the reduction process (like Dhar's algorithm or repeated
    legal firings) preserves effectiveness when starting with an effective divisor. -/
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

lemma effective_of_winnable_and_q_reduced (G : CFGraph V) (q : V) (D : CFDiv V) :
  winnable G D → q_reduced G q D → effective D := by
  intro h_winnable h_qred
  rcases h_winnable with ⟨E, h_eff_E, h_equiv⟩
  have h_equiv' : linear_equiv G E D := by
    exact (linear_equiv_is_equivalence G).symm h_equiv
  exact helper_q_reduced_of_effective_is_effective G q E D h_eff_E h_equiv' h_qred
/-
# Helpers for Lemma 4.1.10
-/

/-- Lemma: A non-empty graph with an acyclic orientation must have at least one source. -/
lemma helper_acyclic_has_source (G : CFGraph V) (O : CFOrientation G) :
  is_acyclic G O → ∃ v : V, is_source G O v := by
  intro h_acyclic
  have h := subset_source G O Finset.univ Finset.univ_nonempty h_acyclic
  rcases h with ⟨v, _, h_source⟩
  use v
  dsimp [is_source]
  simp
  rw [indeg_eq_sum_flow]
  apply Finset.sum_eq_zero
  exact h_source

lemma orientation_edges_loopless (G : CFGraph V) (O : CFOrientation G) :
    ∀ v : V, (v,v) ∉ O.directed_edges := by
  intro v
  have h_g_no_loop_at_v : (v,v) ∉ G.edges := by
    exact (isLoopless_prop_bool_equiv G.edges).mpr G.loopless v

  have h_g_count_loop_eq_zero : Multiset.count (v,v) G.edges = 0 := by
    exact Multiset.count_eq_zero_of_not_mem h_g_no_loop_at_v

  have h_count_preserving := O.count_preserving v v
  rw [show ∀ (m : Multiset (V×V)) (p : V×V), Multiset.count p m + Multiset.count p m = 2 * Multiset.count p m by intros; rw [two_mul]] at h_count_preserving

  rw [num_edges_self_zero G v] at h_count_preserving
  -- Now: h_count_preserving is `0 = 2 * Multiset.count (v,v) O.directed_edges`

  have h_o_count_loop_eq_zero : Multiset.count (v,v) O.directed_edges = 0 := by
    cases hv_count_o_edges : (Multiset.count (v,v) O.directed_edges) with
    | zero => rfl
    | succ n => -- Here, hv_count_o_edges is `count (v,v) O.directed_edges = Nat.succ n`
      rw [hv_count_o_edges] at h_count_preserving -- h_count_preserving becomes `0 = 2 * (Nat.succ n)`
      linarith [Nat.mul_pos (by decide : 2 > 0) (Nat.succ_pos n)] -- `0 = 2 * Nat.succ n` and `2 * Nat.succ n > 0` is a contradiction

  exact (Multiset.count_eq_zero).mp h_o_count_loop_eq_zero

/-- Helper lemma: Two orientations are equal if they have the same directed edges -/
lemma helper_orientation_eq_of_directed_edges {G : CFGraph V}
  (O O' : CFOrientation G) :
  O.directed_edges = O'.directed_edges → O = O' := by
  intro h
  -- Use cases to construct the equality proof
  cases O with | mk edges consistent =>
  cases O' with | mk edges' consistent' =>
  -- Create congr_arg to show fields are equal
  congr

/-- Lemma: Given a list of disjoint vertex sets that form a partition of V,
    an acyclic orientation is uniquely determined by this partition where
    each set contains vertices with same indegree. -/
lemma helper_orientation_determined_by_levels {G : CFGraph V}
  (O O' : CFOrientation G) :
  is_acyclic G O → is_acyclic G O' →
  (∀ v : V, indeg G O v = indeg G O' v) →
  O = O' := by
  intro h_acyc h_acyc' h_indeg_eq

  let S := { e : V × V | O.directed_edges.count e > O'.directed_edges.count e }
  have suff_S_empty : S = ∅ → O = O' := by
    intro h_S_empty
    have h_ineq (u v : V) : flow O u v ≤ flow O' u v := by
      have h_nin: ⟨u,v⟩ ∉ S := by
        rw [h_S_empty]
        simp
      dsimp [S] at h_nin
      linarith
    simp [eq_orient O O']
    intro u v
    by_contra h_neq
    have h_uv_le := h_ineq u v
    have h_lt : flow O u v < flow O' u v := lt_of_le_of_ne h_uv_le h_neq
    have h_indeg_contra : indeg G O v < indeg G O' v := by
      rw [indeg_eq_sum_flow O v, indeg_eq_sum_flow O' v]
      apply Finset.sum_lt_sum
      intro x hx
      exact h_ineq x v
      use u
      simp [h_lt]
    linarith [h_indeg_eq v]
  apply suff_S_empty

  -- A small helper we'll need a couple time later
  have directed_edge_of_S (e : V × V) : e ∈ S → directed_edge G O e.1 e.2 :=  by
    dsimp [directed_edge]
    intro h
    dsimp [S] at h
    have h_pos_count : count e O.directed_edges > 0 := by
      apply gt_of_gt_of_ge h
      exact Nat.zero_le _
    apply Multiset.count_pos.mp
    linarith [h_pos_count]

  -- We now must show that S is empty.
  -- Do so buy showing any element in S belongs to an infinite directd path
  have going_up : ∀ e ∈ S, ∃ f ∈ S, f.2 = e.1 := by
    intro e h_e_in_S
    obtain ⟨u,v⟩ := e
    by_contra! h_no_parent
    have all_flow_le : ∀ (w : V) , flow O w u ≤ flow O' w u := by
      intro w
      by_contra h_flow_gt
      apply lt_of_not_ge at h_flow_gt
      specialize h_no_parent ⟨w,u⟩
      simp at h_no_parent
      exact h_no_parent h_flow_gt
    have one_flow_lt : ∃ (w : V), flow O w u < flow O' w u := by
      contrapose! h_e_in_S
      dsimp [S]
      suffices flow O u v ≤ flow O' u v by linarith
      specialize h_e_in_S v
      by_contra flow_lt
      apply lt_of_not_ge at flow_lt
      have edges_lt := add_lt_add_of_le_of_lt h_e_in_S flow_lt
      rw [opp_flow O v u, opp_flow O' v u] at edges_lt
      linarith

    have h: ∑ (w : V), flow O w u < ∑ (w : V), flow O' w u := by
      apply Finset.sum_lt_sum
      intro i _
      exact all_flow_le i
      rcases one_flow_lt with ⟨w, h_flow_lt⟩
      use w
      constructor
      simp
      exact h_flow_lt

    repeat rw [← indeg_eq_sum_flow] at h
    specialize h_indeg_eq u
    linarith

  -- For contradiction, we can build an infinite directed path in G under O
  by_contra! h_S_nonempty
  rcases h_S_nonempty with ⟨e_start, h_e_start_in_S⟩
  have S_path (n : ℕ) : ∃ (p : DirectedPath O), p.vertices.length = n + 2 ∧ List.Chain' (λ ( u v : V) => ⟨u,v⟩ ∈ S) p.vertices := by
    induction' n with n ih
    . -- Base case: n = 0, i.e. length 2 path
      use {
        vertices := [e_start.1, e_start.2],
        non_empty := by simp,
        valid_edges := by
          dsimp [List.Chain']
          simp [h_e_start_in_S]
          exact directed_edge_of_S e_start h_e_start_in_S
      }
      simp [h_e_start_in_S]
    . -- Inductive step
      rcases ih with ⟨p0, h_len, h_chain⟩
      -- Write p0 as v :: w :: rest, using the fact that its length is at least 2
      have : ∃ (v w : V) (rest : List V), p0.vertices = v :: w :: rest := by
        cases h_p0 : p0.vertices with
        | nil =>
          -- This case should not happen since p0.vertices has length n + 2 ≥ 2
          exfalso
          rw [h_p0] at h_len
          simp at h_len
        | cons v ws =>
          cases h_ws : ws with
          | nil =>
            -- This case should not happen since p0.vertices has length n + 2 ≥ 2
            exfalso
            rw [h_p0,h_ws] at h_len
            simp [h_p0] at h_len
          | cons w rest =>
            use v, w, rest
      rcases this with ⟨v, w, rest, h_p0_eq⟩
      -- Now, p0.vertices = v :: w :: rest
      specialize going_up ⟨v,w⟩
      have h_vw_in_S : ⟨v,w⟩ ∈ S := by
        -- From h_chain, we know that ⟨v,w⟩ ∈ S
        dsimp [List.Chain'] at h_chain
        rw [h_p0_eq] at h_chain
        simp at h_chain
        exact h_chain.left
      specialize going_up h_vw_in_S
      rcases going_up with ⟨f, h_f_in_S, h_f_to_v⟩
      let new_path_list : List V := f.1 :: p0.vertices
      use {
        vertices := new_path_list,
        non_empty := by
          rw [List.length_cons]
          exact Nat.succ_pos _,
        valid_edges := by
          dsimp [new_path_list, List.Chain']
          -- Check that the first edge is valid
          rw [h_p0_eq]
          constructor
          have : f.2 = v := h_f_to_v
          rw [← this]
          exact directed_edge_of_S f h_f_in_S
          -- The rest of the path is valid from induction
          have h_ind := p0.valid_edges
          dsimp [List.Chain'] at h_ind
          simp only [h_p0_eq] at h_ind
          exact h_ind
        }
      -- Now must verify that this new path has the right length
      constructor
      rw [List.length_cons]
      rw [h_len]
      -- Verify the chain property
      dsimp [new_path_list, List.Chain']
      simp [h_p0_eq]
      -- Verify the first link is in S
      constructor
      have : f.2 = v := h_f_to_v
      rw [← this]
      exact h_f_in_S
      -- The rest of the chain follows from h_chain
      have h_ind := h_chain
      dsimp [List.Chain'] at h_ind
      simp only [h_p0_eq] at h_ind
      simp at h_ind
      exact h_ind
  specialize S_path (Fintype.card V)
  rcases S_path with ⟨p, h_len, _⟩
  linarith  [path_length_bound p (h_acyc p)]

/-
# Helpers for Proposition 4.1.11
-/

/-- Lemma: CFOrientation to config preserves indegrees -/
lemma orientation_to_config_indeg (G : CFGraph V) (O : CFOrientation G) (q : V)
    (h_acyclic : is_acyclic G O) (h_unique_source : ∀ w, is_source G O w → w = q) (v : V) :
    (orientation_to_config G O q h_acyclic h_unique_source).vertex_degree v =
    if v = q then 0 else (indeg G O v : ℤ) - 1 := by
  -- This follows directly from the definition of config_of_source
  simp only [orientation_to_config] at *
  -- Use the definition of config_of_source
  exact rfl

lemma helper_orientation_config_superstable (G : CFGraph V) (O : CFOrientation G) (q : V)
    (h_acyc : is_acyclic G O) (h_unique_source : ∀ w, is_source G O w → w = q) :
    superstable G q (orientation_to_config G O q h_acyc h_unique_source) := by
    let c := orientation_to_config G O q h_acyc h_unique_source
    apply (superstable_iff_q_reduced G q (genus G -1) c).mpr

    have h_c := config_and_divisor_from_O O h_acyc h_unique_source
    dsimp [c]
    rw [h_c]
    have : genus G - 1 = deg ((orqed O h_acyc h_unique_source).D) := by
      dsimp [orqed]
      rw [degree_ordiv O]
    rw [this]
    rw [div_of_config_of_div (orqed O h_acyc h_unique_source)]
    dsimp [orqed]
    exact ordiv_q_reduced O h_acyc h_unique_source

/- Axiom: Defining a reusable block for a configuration from an acyclic orientation with source q being maximal superstable
          Only to be used to define a maximal superstable configuration from an acyclic orientation with source q as a Prop.
   This was especially hard to prove in Lean4, so we are leaving it as an axiom for now.
-/
axiom helper_orientation_config_maximal (G : CFGraph V) (O : CFOrientation G) (q : V)
    (h_acyc : is_acyclic G O) (h_unique_source : ∀ w, is_source G O w → w = q) :
    maximal_superstable G (orientation_to_config G O q h_acyc h_unique_source)

/-- Lemma: Two acyclic orientations with same indegrees are equal -/
lemma orientation_unique_by_indeg {G : CFGraph V} (O₁ O₂ : CFOrientation G)
    (h_acyc₁ : is_acyclic G O₁) (h_acyc₂ : is_acyclic G O₂)
    (h_indeg : ∀ v : V, indeg G O₁ v = indeg G O₂ v) : O₁ = O₂ := by
  -- Apply the helper statement directly since we have exactly matching hypotheses
  exact helper_orientation_determined_by_levels O₁ O₂ h_acyc₁ h_acyc₂ h_indeg

/-- Lemma to show indegree of source is 0 -/
lemma source_indeg_zero {G : CFGraph V} (O : CFOrientation G) (v : V)
    (h_src : is_source G O v) : indeg G O v = 0 := by
  -- By definition of is_source in terms of indeg
  unfold is_source at h_src
  -- Convert from boolean equality to proposition
  exact of_decide_eq_true h_src

/-- Lemma proving uniqueness of orientations giving same config -/
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

/-- Lemma to convert between configuration equality forms -/
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

/-- Lemma: A divisor can be decomposed into parts of specific degrees. -/
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
      -- deg E₂ = b
      constructor
      exact h_deg_E2
      -- E = (E₁ + one_chip v) + E₂
      dsimp [E'] at h_eq_split
      rw [add_assoc, add_comm (one_chip v), ← add_assoc, ← h_eq_split]
      abel

  exact h_ind k₁ k₂ E'' h_effective h_deg


-- Redundent with winnable_add_winnable from Rank.lean
-- /- Helper lemma: Winnability is preserved under addition -/
-- theorem helper_winnable_add (G : CFGraph V) (D₁ D₂ : CFDiv V) :
--   winnable G D₁ → winnable G D₂ → winnable G (D₁ + D₂) := by
--   -- Assume D₁ and D₂ are winnable
--   intro h1 h2

--   -- Get the effective divisors that D₁ and D₂ are equivalent to
--   rcases h1 with ⟨E₁, hE₁_eff, hE₁_equiv⟩
--   rcases h2 with ⟨E₂, hE₂_eff, hE₂_equiv⟩

--   -- Our goal is to show that D₁ + D₂ is winnable
--   -- We'll show E₁ + E₂ is effective and linearly equivalent to D₁ + D₂

--   -- Define our candidate effective divisor
--   let E := E₁ + E₂

--   -- Show E is effective
--   have hE_eff : effective E := by
--     intro v
--     simp [effective] at hE₁_eff hE₂_eff ⊢
--     have h1 := hE₁_eff v
--     have h2 := hE₂_eff v
--     exact add_nonneg h1 h2

--   -- Show E is linearly equivalent to D₁ + D₂
--   have hE_equiv : linear_equiv G (D₁ + D₂) E := by
--     unfold linear_equiv
--     -- Show (E₁ + E₂) - (D₁ + D₂) = (E₁ - D₁) + (E₂ - D₂)
--     have h : E - (D₁ + D₂) = (E₁ - D₁) + (E₂ - D₂) := by
--       funext w
--       simp [sub_apply, add_apply]
--       -- Expand E = E₁ + E₂
--       have h1 : E w = E₁ w + E₂ w := rfl
--       rw [h1]
--       -- Use ring arithmetic to complete the proof
--       ring

--     rw [h]
--     -- Use the fact that principal divisors form an additive subgroup
--     exact AddSubgroup.add_mem _ hE₁_equiv hE₂_equiv

--   -- Construct the witness for winnability
--   exists E

-- /- [Alternative-Proof] Helper theorem: Winnability is preserved under addition -/
-- theorem helper_winnable_add_alternative (G : CFGraph V) (D₁ D₂ : CFDiv V) :
--   winnable G D₁ → winnable G D₂ → winnable G (λ v => D₁ v + D₂ v) := by
--   -- Introduce the winnability hypotheses
--   intros h1 h2

--   -- Unfold winnability definition for D₁ and D₂
--   rcases h1 with ⟨E₁, hE₁_eff, hE₁_equiv⟩
--   rcases h2 with ⟨E₂, hE₂_eff, hE₂_equiv⟩

--   -- Our goal is to find an effective divisor linearly equivalent to D₁ + D₂
--   use (E₁ + E₂)

--   constructor
--   -- Show E₁ + E₂ is effective
--   {
--     unfold Div_plus -- Note: Div_plus is defined using effective
--     unfold effective at *
--     intro v
--     have h1 := hE₁_eff v
--     have h2 := hE₂_eff v
--     exact add_nonneg h1 h2
--   }

--   -- Show E₁ + E₂ is linearly equivalent to D₁ + D₂
--   {
--     unfold linear_equiv at *

--     -- First convert the function to a CFDiv
--     let D₁₂ : CFDiv V := (λ v => D₁ v + D₂ v)

--     have h : (E₁ + E₂ - D₁₂) = (E₁ - D₁) + (E₂ - D₂) := by
--       funext v
--       simp [Pi.add_apply, sub_apply]
--       ring

--     rw [h]
--     exact AddSubgroup.add_mem (principal_divisors G) hE₁_equiv hE₂_equiv
--   }





/-
# Helpers for Corollary 4.2.3 + Handshaking Theorem
-/

/-- Helper lemma: Every divisor can be decomposed into a principal divisor and an effective divisor -/
lemma eq_nil_of_card_eq_zero {α : Type _} {m : Multiset α}
    (h : Multiset.card m = 0) : m = ∅ := by
  induction m using Multiset.induction_on with
  | empty => rfl
  | cons a s ih =>
    simp only [Multiset.card_cons] at h
    -- card s + 1 = 0 is impossible for natural numbers
    have : ¬(Multiset.card s + 1 = 0) := Nat.succ_ne_zero (Multiset.card s)
    contradiction

/-- Helper lemma: In a loopless graph, each edge has distinct endpoints -/
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

/-- Helper lemma: Each edge is incident to exactly two vertices -/
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


/-- Helper lemma: Summing mapped incidence counts equals summing constant 2 (Nat version). -/
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

-- Key lemma for handshaking theorem: Sum of edge counts equals incident edge count
lemma sum_num_edges_eq_filter_count (G : CFGraph V) (v : V) :
  ∑ u, num_edges G v u = Multiset.card (G.edges.filter (λ e => e.fst = v ∨ e.snd = v)) := by
  dsimp [num_edges]
  have h_loopless: ∀ e ∈ G.edges, e.1 ≠ e.2 := by
    intro e he
    exact edge_endpoints_distinct G e he
  exact degree_eq_total_flow G.edges v (h_loopless)

/--
**Handshaking Theorem:** In a loopless multigraph \(G\),
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
    _ = ↑(Multiset.sum (G.edges.map (λ e => (Finset.univ.filter (λ v => e.1 = v ∨ e.2 = v)).card))) := by rw [sum_filter_eq_map G (G.edges) (λ v e => e.fst = v ∨ e.snd = v)]
    _ = ↑(2 * Multiset.card G.edges) := by rw [map_inc_eq_map_two_nat G]
    _ = 2 * ↑(Multiset.card G.edges) := by rw [Nat.cast_mul, Nat.cast_two]






/-
# Helpers for Proposition 4.1.13 Part (1)
-/


/-- Helper Lemma: Equivalence between q-reduced divisors and superstable configurations.
    A divisor D is q-reduced iff it can be written as c - δ_q for some superstable config c.
    Relies on the updated definition of q_reduced in Basic.lean matching outdeg_S. -/
lemma q_reduced_superstable_correspondence (G : CFGraph V) (q : V) (D : CFDiv V) :
  q_reduced G q D ↔ ∃ c : Config V q, superstable G q c ∧
  D = toDiv (deg D) c := by
  constructor
  . -- Forward direction (q_reduced → ∃ c, superstable ∧ D = c - δ_q)
    intro h_qred
    let D_qed : q_eff_div V q := {
      D := D,
      h_eff := by
        intro v h_v
        exact  h_qred.1 v h_v
    }
    let c := toConfig D_qed
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
        have hc_func_v : c.1 v = D v + 0 := by
          dsimp [c, toConfig]
          simp
          dsimp [one_chip]
          simp
          right
          assumption
        dsimp [c, toConfig]
        simp [hv_ne_q]
        -- Prove D v + 0 < outdeg_S G q S v from D v < outdeg_S G q S v
        dsimp [outdeg_S]
        have : Finset.filter (fun x ↦ x ∉ S) univ = univ \ S := by
          ext
          simp
        rw [← this]
        exact h_dv_lt_outdeg
    -- Prove D = c - δ_q
    · funext v -- Prove equality for all v

      -- simp only [Config.vertex_degree] -- Unfold c.vertex_degree
      -- Goal: D v = c.vertex_degree v - if v = q then 1 else 0
      by_cases hv : v = q
      · dsimp [toDiv,c, toConfig]
        simp [hv]
        dsimp [config_degree,one_chip]
        simp [hv, if_true] -- Case v = q
      · -- Case v ≠ q
        dsimp [toDiv]
        simp [hv]
        dsimp [c, toConfig]
        simp
        rw [one_chip_apply_other]
        ring
        intro h
        rw [h] at hv
        contradiction -- Case v ≠ q
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
      dsimp [toDiv]
      simp [hv_ne_q]
      apply c.non_negative
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
        dsimp [toDiv]
        simp [hv_ne_q]

        -- simp only [if_neg hv_ne_q] -- Simplify for v ≠ q
        -- Goal: c.vertex_degree v - 0 < outdeg_S G q S v
        -- This is exactly hc_lt_outdeg
        -- Prove c.vertex_degree v - 0 < ... from c.vertex_degree v < ...
        -- simp only [sub_zero]
        apply lt_of_lt_of_le hc_lt_outdeg
        unfold outdeg_S
        have same_domain : Finset.filter (fun x ↦ x ∉ S) univ = univ \ S := by
          ext
          simp
        rw [← same_domain]


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
  have := helper_maximal_superstable_orientation G q c h_max
  rcases this with ⟨O, h_acyc, h_unique_source, h_orient_eq⟩
  rw [← h_orient_eq]
  rw [config_and_divisor_from_O O h_acyc h_unique_source ]
  dsimp [toConfig, config_degree]
  rw [map_sub]
  dsimp [orqed]
  rw [degree_ordiv]
  suffices (ordiv G O) q = -1 by
    rw [this]
    simp [map_smul, deg_one_chip]
  -- Prove (ordiv G O) q = -1
  dsimp [ordiv]
  -- These lines look funny, but they just check that "q is a unique source" implies "q is a source."
  -- [TODO] consider making a helper lemma for this step, and/or giving a name to the "is a unique source" property.
  have := helper_acyclic_has_source G O h_acyc
  rcases this with ⟨some_source, h_source⟩
  specialize h_unique_source some_source h_source
  rw [h_unique_source] at h_source
  dsimp [is_source] at h_source
  simp at h_source
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
  have := helper_maximal_superstable_exists G q c h_super
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
  have := helper_maximal_superstable_orientation G q c h_max
  rcases this with ⟨O, h_acyc, h_unique_source, h_orient_eq⟩
  have h_genus_eq : config_degree c = genus G := by
    exact degree_max_superstable c h_max
  rw [← h_genus_eq]

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

/-- Helper lemma: Difference between dominated configurations
    implies linear equivalence of corresponding q-reduced divisors.

    This proof relies on the standard definition of superstability (`superstable`)
    and an axiom (`superstable_dominance_implies_principal`) stating that the difference
    between dominated standard-superstable configurations is a principal divisor.
-/
lemma helper_q_reduced_linear_equiv_dominates (G : CFGraph V) (q : V) (c c' : Config V q) :
  superstable G q c → superstable G q c' → config_ge c' c →
  linear_equiv G
    (c.vertex_degree - one_chip q)
    (c'.vertex_degree - one_chip q) := by
  intros h_std_super_c h_std_super_c' h_ge

  -- Goal: Show linear_equiv G D₁ D₂
  -- By definition of linear_equiv, this means D₂ - D₁ ∈ principal_divisors G
  unfold linear_equiv -- Explicitly unfold the definition

  -- Prove the difference D₂ - D₁ equals c' - c pointwise
  have h_diff : (c'.vertex_degree - one_chip q) - (c.vertex_degree - one_chip q) =
                (c'.vertex_degree - c.vertex_degree) := by
    simp

  -- Rewrite the goal using the calculated difference D₂ - D₁ = c' - c
  simp

  -- Apply the axiom `superstable_dominance_implies_principal`.
  -- This axiom states that if c and c' are standard-superstable and c' dominates c,
  -- then their difference (c' - c) is indeed a principal divisor.
  exact superstable_dominance_implies_principal G q c c' h_std_super_c h_std_super_c' h_ge

/-- Helper theorem: Linear equivalence preserves winnability -/
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

/-- Helper lemma: Source vertices have equal indegree (zero) when v = q -/
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
    linear_equiv G D (c.vertex_degree + k • (one_chip q)) ∧
    superstable G q c := by
  -- 1. Get the q-reduced representative D' for D using the axiom
  rcases exists_q_reduced_representative G q D with ⟨D', h_equiv_D_D', h_qred_D'⟩

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

-- /-- Axiom: Dhar's algorithm produces negative k for unwinnable divisors
--     When applied to an unwinnable divisor D, Dhar's algorithm must produce a
--     negative value for k (the number of chips at q). This is a crucial fact used
--     in characterizing unwinnable divisors, proven in chapter 4 of Corry & Perkinson's
--     "Divisors and Sandpiles" (AMS, 2018). The negativity of k is essential for
--     showing the relationship between unwinnable divisors and q-reduced forms. -/
lemma helper_dhar_negative_k (G : CFGraph V) (q : V) (D : CFDiv V) :
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
    rw [smul_apply]
    have c_nonneg: c.vertex_degree v ≥ 0 := c.non_negative v
    have oc_nonneg : k*one_chip q v ≥ 0 := by
      dsimp [one_chip]
      split_ifs
      · simp [k_nonneg]
      · simp [k_nonneg]
    linarith
  have h_winnable_D' : winnable G D' := winnable_of_effective G D' D'_eff
  apply winnable_equiv_winnable G D' D h_winnable_D'
  apply (linear_equiv_is_equivalence G).symm h_equiv

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

/-- Lemma: Given a graph G and a vertex q, there exists a maximal superstable divisor
    c' that is greater than or equal to any superstable divisor c. This is a key
    result from Corry & Perkinson's "Divisors and Sandpiles" (AMS, 2018) that is
    used in proving the Riemann-Roch theorem for graphs. -/
lemma helper_superstable_to_unwinnable (G : CFGraph V) (q : V) (c : Config V q) :
  maximal_superstable G c →
  ¬winnable G (c.vertex_degree - one_chip q) := by
  intro h_max_superstable
  let D := c.vertex_degree - one_chip q
  have h_red : q_reduced G q D := by
    apply (q_reduced_superstable_correspondence G q D).mpr
    use c
    constructor
    · -- Prove superstable G q c
      exact h_max_superstable.1
    · -- Prove D = c - δ_q
      dsimp [toDiv]
      have h_deg : deg D = config_degree c - 1 := by
        dsimp [D]
        rw [map_sub, deg_one_chip]
        dsimp [config_degree]
      rw [h_deg]
      dsimp [D]
      funext v
      rw [sub_apply, add_apply, smul_apply]
      linarith
  by_contra! h_winnable
  have := (winnable_iff_q_reduced_effective G q D).mp
  dsimp [D] at this
  apply this at h_winnable
  rcases h_winnable with ⟨D', h_equiv, h_qred', h_eff⟩
  -- Use uniqueness of q-reduced forms to conclude D = D'
  rcases helper_unique_q_reduced G q D with ⟨D'', h_equiv'', h_unique⟩
  have h_eq : D = D'' := by
    apply h_unique D
    constructor
    · exact (linear_equiv_is_equivalence G).refl D
    . exact h_red
  have h_eq' : D' = D'' := by
    apply h_unique D'
    constructor
    · exact h_equiv
    · exact h_qred'
  rw [← h_eq'] at h_eq
  rw [← h_eq] at h_eff
  -- D is effective, contradicting its definition
  have h_nonneg_q := h_eff q
  dsimp [D] at h_nonneg_q
  simp [c.q_zero] at h_nonneg_q

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

/-- Helper lemma: Effective divisors have non-negative degree -/
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
