import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import ChipFiringWithLean.Basic
-- import Paperproof

set_option linter.unusedVariables false
set_option trace.split.failure true
set_option linter.unusedSectionVars false

open Multiset Finset

-- Assume V is a finite, nonempty type with decidable equality
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]

abbrev Vtilde (q : V) : Finset V :=
  univ.filter (λ v => v ≠ q)

/-- A nonnegative configuration on a graph G with respect to a distinguished vertex q.
    Represents an element of ℤ(V\{q}) ⊆ ℤV with non-negativity constraints on V\{q}.

    Fields:
    * vertex_degree - Assignment of integers to vertices
    * non_negative_except_q - Proof that all values except at q are non-negative

    For convenience, vertex_degree is defined on all of V, and set to be 0 at q itself.

    **Note** that this structure assumes that all vertex degrees are nonnegaitve, which differs from the definition in [Corry-Perkinson], Definition 2.9. -/
structure Config (V : Type) [DecidableEq V] [Fintype V] [Nonempty V] (q : V) where
  /-- Assignment of integers to vertices representing the number of chips at each vertex -/
  (vertex_degree : CFDiv V)
  /-- Fix vertex_degree q = 0 for convenience -/
  (q_zero : vertex_degree q = 0)
  /-- Proof that all vertices except q have non-negative values -/
  (non_negative : ∀ v : V, vertex_degree v ≥ 0)

/-- The degree of a configuration is the sum of all values except at q.
    deg(c) = ∑_{v ∈ V\{q}} c(v) -/
def config_degree {q : V} (c : Config V q) : ℤ :=
  deg (c.vertex_degree)

/-- Convert a configuration to a divisor of specified
  degree d, but adding an appropraite number of chips
  at q. -/
def toDiv {q : V} (d : ℤ) (c : Config V q) : CFDiv V :=
  c.vertex_degree + (d - config_degree c) • (one_chip q)

lemma eq_config_iff_eq_vertex_degree {q : V} (c₁ c₂ : Config V q) :
  c₁ = c₂ ↔ c₁.vertex_degree = c₂.vertex_degree := by
  constructor
  -- Forward direction is clear
  intro h_eq
  rw [h_eq]
  -- Reverse direction takes more
  intro h_eq
  obtain ⟨vd₁, _, _⟩ := c₁
  obtain ⟨vd₂, _, _⟩ := c₂
  simp only [Config.mk.injEq]
  funext v
  apply congrFun h_eq v

lemma eq_config_iff_eq_div {q : V} (d : ℤ) (c₁ c₂ : Config V q) : c₁ = c₂ ↔ toDiv d c₁ = toDiv d c₂ := by
  constructor
  -- Forward direction is clear
  intro h_eq
  rw [h_eq]
  -- Reverse direction takes more
  intro h_eq
  apply congrFun at h_eq
  suffices h: c₁.vertex_degree = c₂.vertex_degree by
    obtain ⟨vd₁, _, _⟩ := c₁
    obtain ⟨vd₂, _, _⟩ := c₂
    simp only [Config.mk.injEq]
    funext v
    apply congrFun h v
  funext v
  specialize h_eq v
  dsimp [toDiv] at h_eq
  by_cases h_v : q = v
  . -- Case v = q
    rw [← h_v]
    rw [c₁.q_zero, c₂.q_zero]
  . -- Case v ≠ q
    simp [h_v] at h_eq
    exact h_eq

def to_qed {q : V} (d : ℤ) (c : Config V q) : q_eff_div V q :=
  {
    D := toDiv d c,
    h_eff := by
      intro v h_v
      dsimp [toDiv]
      simp [h_v]
      exact c.non_negative v
  }
def toConfig {q : V} (D : q_eff_div V q) : Config V q := {
  vertex_degree := D.D - (D.D q) • (one_chip q)
  q_zero := by
    rw [sub_apply,smul_apply]
    dsimp [one_chip]
    simp
  non_negative := by
    intro v
    by_cases h_v : v = q
    · -- Case v = q
      simp [h_v]
    . -- Case v ≠ q
      simp [h_v]
      exact D.h_eff v h_v
}

def config_degree_div_degree {q : V} (D : q_eff_div V q) : deg D.D = D.D q + config_degree (toConfig D) := by
  dsimp [config_degree, toConfig, one_chip]
  simp

lemma config_of_div_of_config (c : Config V q) (d : ℤ)  :
  toConfig (to_qed d c) = c := by
  rcases c with ⟨vertex_degree, q_zero, non_negative⟩
  dsimp [to_qed, toConfig]
  simp
  apply funext
  intro v
  by_cases h_v : v = q
  . -- Case v = q
    simp [h_v]
    rw [q_zero]
  . -- Case v ≠ q
    dsimp [toDiv, one_chip]
    simp [h_v]

lemma qeff_divs_equal (D1 D2 : q_eff_div V q) :
  D1 = D2 ↔ D1.D = D2.D := by
  constructor
  intro h_eq
  rw [h_eq]
  -- Converse is the interesting direction
  intro h_eq
  rcases D1 with ⟨D1_D, D1_h_eff⟩
  rcases D2 with ⟨D2_D, D2_h_eff⟩
  simp
  simp at h_eq
  exact h_eq

lemma div_of_config_of_div (D : q_eff_div V q) :
  toDiv (deg D.D) (toConfig D) = D.D := by
  -- apply (qeff_divs_equal (to_qed (deg D.D) (toConfig D)) D).mpr
  -- dsimp [to_qe]
  funext v
  dsimp [toDiv]
  by_cases h: v ∈ Vtilde q
  . -- Case v ∈ Vtilde q
    dsimp [toConfig]
    have : v ≠ q := by
      intro h_eq_q
      rw [h_eq_q] at h
      simp at h
    simp [this]
  . -- Case v ∉ Vtilde q
    have : v = q := by
      contrapose! h
      simp [h]
    rw [this]
    unfold toConfig config_degree
    simp

@[simp] lemma eval_toDiv_q {q : V} (d : ℤ) (c : Config V q) :
  toDiv d c q = d - config_degree c := by
  dsimp [toDiv]
  simp [c.q_zero]

@[simp] lemma eval_toDiv_ne_q {q v : V} (d : ℤ) (c : Config V q) (h_v : v ≠ q) :
  toDiv d c v = c.vertex_degree v := by
  dsimp [toDiv]
  simp [h_v]


lemma config_eff {q : V} (d : ℤ) (c : Config V q) : effective (toDiv d c) ↔ d ≥ config_degree c := by
  constructor
  -- Effective implies d ≥ config_degree
  intro h_eff
  have h := h_eff q
  rw [eval_toDiv_q] at h
  linarith
  -- d ≥ config_degree implies effective
  intro h_deg v
  by_cases h_v : v = q
  · -- Case v = q
    simp [h_v, h_deg]
  · -- Case v ≠ q
    simp [h_v]
    exact c.non_negative v

/-- Ordering on configurations: c ≥ c' if c(v) ≥ c'(v) for all v ∈ V.
    This is a pointwise comparison of the number of chips at each vertex.
    It also compares degree at v = q, but this is not a problem since that is always assumed zero.
    -/
def config_ge {q : V} (c c' : Config V q) : Prop :=
  ∀ v : V, c.vertex_degree v ≥ c'.vertex_degree v

lemma config_eq_of_ge_and_degree {q : V} {c1 c2 : Config V q} (h_ge : config_ge c1 c2) (h_deg : config_degree c1 = config_degree c2) : c1 = c2 := by
  apply (eq_config_iff_eq_vertex_degree c1 c2).mpr
  dsimp [config_ge] at h_ge
  dsimp [config_degree, deg] at h_deg
  have h_le : ∀ v : V, c2.vertex_degree v ≤ c1.vertex_degree v := by
    intro v
    specialize h_ge v
    linarith
  suffices ∀ v : V, c1.vertex_degree v = c2.vertex_degree v by
    funext v
    specialize this v
    exact this
  contrapose! h_deg with h_ne
  rcases h_ne with ⟨v, h_v_ne⟩
  have h_gt : c2.vertex_degree v < c1.vertex_degree v := by
    specialize h_ge v
    apply lt_of_le_of_ne h_ge
    contrapose! h_v_ne
    simp [h_v_ne]
  suffices config_degree c2 < config_degree c1 by
    apply ne_of_gt this
  dsimp [config_degree, deg]
  refine Finset.sum_lt_sum ?_ ?_
  intro i _
  specialize h_le i
  exact h_le
  use v
  simp
  exact h_gt

instance : PartialOrder (Config V q) := {
  le := λ c₁ c₂ => c₁.vertex_degree ≤ c₂.vertex_degree,
  le_refl := by
    intro a
    simp
   ,
  le_trans := by
    intro c1 c2 c3 c1_le_c2 c2_le_c3
    exact le_trans c1_le_c2 c2_le_c3
  ,
  le_antisymm := by
    intro c1 c2 h_le h_ge
    have h_eq := le_antisymm h_le h_ge

    exact (eq_config_iff_eq_vertex_degree c1 c2).mpr h_eq
}

-- Definition of the out-degree of a vertex v ∈ S with respect to a subset S ⊆ V \ {q}
-- This counts edges from v to vertices *outside* S.
-- outdeg_S(v) = |{ (v, w) ∈ E | w ∈ V \ S }|
-- The definition does not enforce v ∈ S, though it is only used in that case.
def outdeg_S (G : CFGraph V) (q : V) (S : Finset V) (v : V) : ℤ :=
  -- Sum num_edges from v to w, where w is not in S
  ∑ w ∈ (univ \ S), (num_edges G v w : ℤ)

/- A configuration c is superstable if for every non-empty subset S of V \ {q}, there is at least one vertex v in S that cannot fire without borrowing.
[Corry-Perkinson], Definition 3.12 -/
def superstable (G : CFGraph V) (q : V) (c : Config V q) : Prop :=
  ∀ S ⊆  Vtilde q, S.Nonempty →
    ∃ v ∈ S, c.vertex_degree v < outdeg_S G q S v

/- [Corry-Perkinson], Remark 3.14 -/
lemma superstable_iff_q_reduced (G : CFGraph V) (q : V) (d : ℤ) (c : Config V q) :
  superstable G q c ↔ q_reduced G q (toDiv d c) := by

  -- Little rewriting needed later
  have comp_eq (S : Finset V): univ \ S = Finset.filter (λ w => w ∉ S) univ := by
    ext w
    simp

  dsimp [superstable, q_reduced]
  constructor
  -- Forward direction
  intro h_superstable
  constructor
  -- Show c is nonnegative away from v
  intro v hv_ne_q
  dsimp [toDiv]
  simp [hv_ne_q]
  exact c.non_negative v
  -- Show the outdegree condition
  intro S hS_subset hS_nonempty

  specialize h_superstable S hS_subset hS_nonempty
  rcases h_superstable with ⟨v, hv_in_S, hv_outdeg⟩
  use v
  constructor
  exact hv_in_S
  dsimp [outdeg_S] at hv_outdeg
  have h_v_ne_q : v ≠ q := by
    intro hv_eq_q
    rw [hv_eq_q] at hv_in_S
    have h := hS_subset hv_in_S
    simp at h
  rw [eval_toDiv_ne_q d c h_v_ne_q]
  rw [← comp_eq S]
  refine lt_of_le_of_lt  ?_ hv_outdeg
  apply le_refl
  -- Reverse direction
  intro h_q_reduced
  rcases h_q_reduced with ⟨h_nonneg, h_outdeg⟩
  intro S hS_subset hS_nonempty
  specialize h_outdeg S hS_subset hS_nonempty
  rcases h_outdeg with ⟨v, hv_in_S, hv_outdeg⟩
  use v
  refine ⟨hv_in_S, ?_⟩
  dsimp [toDiv] at hv_outdeg
  have h_v_neq_q : v ≠ q := by
    intro hv_eq_q
    rw [hv_eq_q] at hv_in_S
    have h := hS_subset hv_in_S
    simp at h
  simp [h_v_neq_q] at hv_outdeg
  dsimp [outdeg_S]
  rw [comp_eq S]
  exact hv_outdeg




/-- Helper Lemma: Equivalence between q-reduced divisors and superstable configurations.
    A divisor D is q-reduced iff it can be written as c - δ_q for some superstable config c.-/
lemma q_reduced_superstable_correspondence (G : CFGraph V) (q : V) (D : CFDiv V) :
  q_reduced G q D ↔ ∃ c : Config V q, superstable G q c ∧
  D = toDiv (deg D) c := by
  constructor
  . -- Forward direction (q_reduced → ∃ c, superstable ∧ D = c - δ_q)
    intro h_qred
    let D_qed : q_eff_div V q := {
      D := D,
      h_eff := h_qred.1
    }
    let c := toConfig D_qed; use c
    have D_eq : D = toDiv (deg D) c := by
      have := div_of_config_of_div D_qed
      rw [div_of_config_of_div D_qed]
    rw [D_eq] at h_qred
    rw [superstable_iff_q_reduced G q (deg D) c]
    exact ⟨h_qred, D_eq⟩
  -- Backward direction (∃ c, superstable ∧ D = c - δ_q → q_reduced)
  · intro h_exists
    rcases h_exists with ⟨c, h_super, D_eq⟩
    rw [D_eq]
    rw [← superstable_iff_q_reduced G q (deg D) c]
    exact h_super


/-- A maximal superstable configuration has no legal firings and is not ≤ any other superstable configuration. -/
def maximal_superstable {q : V} (G : CFGraph V) (c : Config V q) : Prop :=
  superstable G q c ∧ ∀ c' : Config V q, superstable G q c' → config_ge c' c → c' = c

lemma smul_one_chip (k : ℤ) (v_chip : V) :
  (k • one_chip v_chip) = (fun v => if v = v_chip then k else 0) := by
  funext v
  rw [Pi.smul_apply]; unfold one_chip
  split_ifs with h
  · simp -- Goal is k • 1 = k
  · simp -- Goal is k • 0 = 0

-- Helper lemma: If D₁ ~ D₂, then D₁ + D ~ D₂ + D
lemma linear_equiv_add_congr_right_local (G : CFGraph V) (D_add : CFDiv V) {D1 D2 : CFDiv V} (h : linear_equiv G D1 D2) :
  linear_equiv G (D1 + D_add) (D2 + D_add) := by
  unfold linear_equiv at h ⊢
  have h_eq : (D2 + D_add) - (D1 + D_add) = D2 - D1 := by abel
  rw [h_eq]
  exact h


/-- Subtracting a chip at q from a superstable configuration gives an unwinnable divisor. -/
lemma helper_superstable_to_unwinnable {G : CFGraph V} (h_conn : graph_connected G) (q : V) (c : Config V q) :
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
  have := (winnable_iff_q_reduced_effective h_conn q D).mp
  dsimp [D] at this
  apply this at h_winnable
  rcases h_winnable with ⟨D', h_equiv, h_qred', h_eff⟩
  -- Use uniqueness of q-reduced forms to conclude D = D'
  rcases unique_q_reduced h_conn q D with ⟨D'', h_equiv'', h_unique⟩
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


/-
## Burn lists and their properties.
This section formalizes what is needed from Dhar's burning algorithm. The main purpose is to prove the correspondence between maximal superstable configurations and orientations.
-/


/-- Definition: A burn list for a Configuraton c is a list [v_1, v_2, ..., v_n, q] of distinct vertices ending at q,
  where the following condition holds at each vertex *except q* (which plays a special role):
  if S is the set V \ {v_1, ..., v_(n-1)} (which contains v_n), then the out-degree of v_n with
  respect to S is greater than the number of chips at v_n. -/
def is_burn_list (G : CFGraph V) {q : V} (c : Config V q) (L : List V) : Prop :=
  match L with
  | [] => False
  | [x] => (x = q)
  | v :: w :: rest =>
      outdeg_S G q (univ \ (w :: rest).toFinset) v > c.vertex_degree v
      -- v isn't in the set made out of w :: rest
      ∧ ¬ (w :: rest).contains v
      ∧ is_burn_list G c (w :: rest)

lemma burn_list_contains_q (G : CFGraph V) {q : V} (c : Config V q) (L : List V) (h_bl : is_burn_list G c L) :
  L.contains q := by
  induction L with
  | nil =>
    dsimp [is_burn_list] at h_bl
  | cons v rest ih =>
    cases rest with
    | nil =>
      dsimp [is_burn_list] at h_bl
      rw [h_bl]
      simp
    | cons w rest' =>
      dsimp [is_burn_list] at h_bl
      rcases h_bl with ⟨h_outdeg, h_not_in_rest, h_rest_burn_list⟩
      specialize ih h_rest_burn_list
      simp
      simp at ih
      simp [ih]

lemma extend_burn_list (G : CFGraph V) {q : V} (c : Config V q) (h_ss : superstable G q c) (L : List V) : is_burn_list G c L → (∃ v : V, ¬ L.contains v) → (∃ w : V, w ∉ L.toFinset ∧ is_burn_list G c (w :: L)) := by
  intro h_bl h_exists_v
  let S := univ \ L.toFinset
  have h_S_ne : S.Nonempty := by
    rcases h_exists_v with ⟨v, h_v_not_in_L⟩
    use v
    dsimp [S]
    simp
    contrapose! h_v_not_in_L with h_raa
    simp [h_raa]
  have h_S_Vtilde : S ⊆ Vtilde q := by
    intro v h_v_in_S
    dsimp [Vtilde]
    simp
    contrapose! h_v_in_S with h_eq
    rw [h_eq]
    dsimp [S]
    simp
    -- Goal is not: q ∈ L
    have := burn_list_contains_q G c L h_bl
    simp at this
    exact this
  specialize h_ss S h_S_Vtilde h_S_ne
  rcases h_ss with ⟨v, hv_in_S, hv_outdeg⟩
  use v
  dsimp [S] at hv_outdeg hv_in_S -- To get L to simplify after matching
  match L with
  | [] =>
    exfalso
    dsimp [is_burn_list] at h_bl
  | h :: t =>
    dsimp [is_burn_list]
    -- Unpack all the conjunctions and use hypotheses one by one
    constructor
    . simp at hv_in_S
      simp
      exact hv_in_S
    constructor
    . exact hv_outdeg
    constructor
    simp
    constructor
    intro h
    rw [h] at hv_in_S
    simp at hv_in_S
    simp at hv_in_S
    exact hv_in_S.2
    exact h_bl

structure burn_list (G : CFGraph V) {q : V} (c : Config V q) where
  (list : List V)
  (h_burn_list : is_burn_list G c list)

lemma burn_list_helper (G : CFGraph V) {q : V} (c : Config V q) (h_ss : superstable G q c) (n : ℕ) : (n < Finset.card (univ : Finset V))→ ∃ (L : List V), L.toFinset.card = n+1 ∧ is_burn_list G c L := by
  intro h_n_lt_card_V
  induction n with
  | zero =>
    use [q]
    constructor
    simp
    dsimp [is_burn_list]
  | succ n ih =>
    have ih_L : n < (univ : Finset V).card := by
      linarith
    apply ih at ih_L
    rcases ih_L with ⟨L, h_L_length, h_L_burn_list⟩
    have h_exists_v : ∃ v : V, ¬ L.contains v := by
      have h_card_L_le : L.toFinset.card < (univ : Finset V).card := by
        rw [← h_L_length] at h_n_lt_card_V
        linarith
      have : ∃ v : V, v ∉ L.toFinset := by
        refine not_forall.mp ?_
        intro h_all_in_L
        have : (univ : Finset V) ⊆ L.toFinset := by
          intro v _
          specialize h_all_in_L v
          exact h_all_in_L
        have bad_ineq : (univ : Finset V).card ≤ L.toFinset.card := Finset.card_le_card this
        linarith
      rcases this with ⟨v, h_v_not_in_L⟩
      use v
      contrapose! h_v_not_in_L with h_all_in_L
      simp at h_all_in_L
      simp [h_all_in_L]
    have := extend_burn_list G c h_ss L h_L_burn_list h_exists_v
    rcases this with ⟨w, h_w_burn_list⟩
    use w :: L
    constructor
    . -- Show cardinality is n+2
      rw [List.toFinset_cons]
      rw [card_insert_eq_ite]
      -- Need: w ∉ L.toFinset
      simp [h_w_burn_list.1]
      rw [h_L_length]
    . -- Show the tail is a burn list
      exact h_w_burn_list.2

lemma superstable_burn_list (G : CFGraph V) {q : V} (c : Config V q) (h_ss : superstable G q c) : ∃ L : burn_list G c, ∀ v : V, v ∈ L.list := by
  have h_card_V : (univ : Finset V).card ≥ 1 := by
    have h_nonempty : Nonempty V := by infer_instance
    have h_card_pos : (univ : Finset V).card > 0 := Fintype.card_pos_iff.mpr h_nonempty
    linarith
  have : (univ : Finset V).card - 1 < (univ : Finset V).card := by
    simp
    -- Now show Fintype.card V > 0, so that the subtraction makes sense
    apply Fintype.card_pos_iff.mpr
    infer_instance
  have h_burn_list := burn_list_helper G c h_ss ((univ : Finset V).card - 1) this
  rcases h_burn_list with ⟨L, h_L_length, h_L_burn_list⟩
  have h_L_card : L.toFinset.card = (univ : Finset V).card := by
    simp [h_L_length]
    apply Nat.sub_add_cancel
    exact h_card_V
  use burn_list.mk L h_L_burn_list
  intro v
  simp
  -- Goal : v ∈ L
  suffices (univ : Finset V) ⊆ L.toFinset by
    have := this (Finset.mem_univ v)
    simp at this
    exact this
  apply univ_subset_iff.mpr
  -- Goal: L.toFinset = univ
  exact (card_eq_iff_eq_univ L.toFinset).mp h_L_card

-- The following lemmas establish the necessary properties of the orientation to be defined from the burn order.

def burn_flow {G : CFGraph V} {q : V} {c : Config V q} (L : burn_list G c) : (V × V) → ℕ :=
  λ e => if (e.1 ∈ L.list) ∧ (L.list.idxOf e.2 < L.list.idxOf e.1) then num_edges G e.1 e.2 else 0

lemma burn_flow_reverse {G : CFGraph V} {q : V} {c : Config V q} (L : burn_list G c) (h_full : ∀ v : V, v ∈ L.list) : ∀ (u v : V), (burn_flow L ⟨u, v⟩) + (burn_flow L ⟨v, u⟩) = num_edges G u v := by
  intro u v
  dsimp [burn_flow]
  by_cases h_uv : L.list.idxOf v < L.list.idxOf u
  . -- Case: indexOf v < indexOf u
    simp [h_uv, h_full u, h_full v]
    intro h
    linarith
  . -- Case: indexOf v ≥ indexOf u
    by_cases h_eq : L.list.idxOf u = L.list.idxOf v
    . -- Subcase: indexOf u < indexOf v
      simp [h_eq]
      have : u = v := (List.idxOf_inj (h_full u)).mp h_eq
      rw [this, num_edges_self_zero G v]
    . -- Subcase: indexOf u > indexOf v
      have h_uv' : L.list.idxOf u < L.list.idxOf v := by
        simp at h_uv h_eq
        exact lt_of_le_of_ne h_uv h_eq
      simp [h_uv',h_uv, h_full v]
      exact num_edges_symmetric G v u

lemma burn_flow_directed {G : CFGraph V} {q : V} {c : Config V q} (L : burn_list G c) (h_full : ∀ v : V, v ∈ L.list) : ∀ (u v : V), burn_flow L ⟨u,v⟩ = 0 ∨ burn_flow L ⟨v,u⟩ = 0 := by
  intro u v
  dsimp [burn_flow]
  by_cases h_uv : L.list.idxOf v < L.list.idxOf u
  . -- Case: indexOf v < indexOf u
    simp [h_uv, h_full u, h_full v]
    right
    intro h
    linarith
  . -- Case: indexOf v ≥ indexOf u
    by_cases h_eq : L.list.idxOf u = L.list.idxOf v
    . -- Subcase: indexOf u = indexOf v
      simp [h_eq]
    . -- Subcase: indexOf u > indexOf v
      have h_uv' : L.list.idxOf u < L.list.idxOf v := by
        simp at h_uv h_eq
        exact lt_of_le_of_ne h_uv h_eq
      simp [h_uv',h_uv, h_full v]

lemma burnin_degree {G : CFGraph V} {q : V} {c : Config V q} (L : burn_list G c) (v : V) (h_pres : v ∈ L.list) (h_ne : v ≠ q): ∑ (w : V), burn_flow L ⟨w,v⟩ > c.vertex_degree v := by
  let h_bl := L.h_burn_list
  cases h: L.list with
  | nil =>
    rw [h] at h_bl
    dsimp [is_burn_list] at h_bl
  | cons x rest =>
    cases h' : rest with
    | nil =>
      rw [h'] at h
      rw [h] at h_bl
      dsimp [is_burn_list] at h_bl
      -- So x = q
      simp [h] at h_pres
      rw [h_pres, ← h_bl] at h_ne
      contradiction
    | cons y rest' =>
      rw [h'] at h
      rw [h] at h_bl
      dsimp [is_burn_list] at h_bl
      -- Need to analyze the position of v in the list
      by_cases h_vx : v = x
      . -- Case: v = x
        rw [← h_vx] at h_bl
        suffices ∑ (w : V), burn_flow L ⟨w,v⟩ ≥ outdeg_S G q (univ \ (y :: rest').toFinset) v by
          linarith [this, h_bl.1]
        dsimp [burn_flow]
        have ind_v : L.list.idxOf v = 0 := by
          rw [h_vx,h]
          simp
        simp only [ind_v]
        have h_ineq := h_bl.1
        have h_above : ∀ (x : V), x ∈ L.list ∧ 0 < List.idxOf x L.list ↔ x ∈ rest := by
          intro w
          rw [← h'] at h
          rw [h]
          simp
          have : 0 < List.idxOf w (x :: rest) ↔ 0 ≠ List.idxOf w (x :: rest) := by
            constructor
            . intro h_pos h_eq
              rw [h_eq] at h_pos
              linarith
            . intro h_neq
              simp at h_neq
              apply Nat.zero_lt_of_ne_zero
              contrapose! h_neq with h_eq_zero
              rw [h_eq_zero]
          rw [this]
          have : 0 ≠ List.idxOf w (x :: rest) ↔ w ≠ x := by
            constructor
            . intro h_neq
              contrapose! h_neq with h_eq
              rw [h_eq]
              simp
            . intro h_neq
              rw [List.idxOf_cons_ne]
              simp
              intro h
              rw [h] at h_neq
              contradiction
          rw [this]
          constructor
          . -- Forward direction
            intro h_w
            by_contra!
            simp [this] at h_w
          . -- Reverse direction
            intro h_w_in_rest
            simp [h_w_in_rest]
            by_contra!
            rw [this] at h_w_in_rest
            have := h_bl.2.1
            rw [h_vx] at this
            rw [← h'] at this
            absurd this
            simp [h_w_in_rest]
        simp only [h_above]
        dsimp [outdeg_S]
        rw [← h']
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
        simp
        have : Finset.filter (Membership.mem rest) univ = rest.toFinset := by
          ext w
          simp
        rw [this]
        apply sum_le_sum
        intro i _
        rw [num_edges_symmetric G i v]
      . -- Case: v ≠ x
        let L' := burn_list.mk (y :: rest') (h_bl.2.2)
        have h_v_in_L' : v ∈ L'.list := by
          dsimp [L']
          rw [← h']
          rw [← h'] at h
          rw [h] at h_pres
          simp [h_vx] at h_pres
          exact h_pres
        have h_step : ∀ (w : V), burn_flow L ⟨w,v⟩ = burn_flow L' ⟨w,v⟩ := by
          have h_x_nin_rest: x ∉ rest := by
            have := L.h_burn_list
            rw [h] at this
            have := this.2.1
            rw [h']
            simp at this
            simp [this]
          intro w
          dsimp [burn_flow]
          rw [h]
          dsimp [L']
          rw [← h'] at *
          rw [List.idxOf_cons_ne]
          by_cases h_wx : w = x
          . -- Subcase: w = x
            rw [h_wx]
            rw [h'] at h_x_nin_rest
            dsimp [L']
            simp [h_x_nin_rest]
          . -- Subcase: w ≠ x
            simp [h_wx]
            repeat rw [List.idxOf_cons_ne]
            dsimp [L']
            simp
            contrapose! h_wx
            rw [h_wx]
          contrapose! h_vx
          rw [h_vx]
        simp only [h_step]
        have h_ind := burnin_degree L' v h_v_in_L' h_ne
        exact h_ind
termination_by L.list.length
decreasing_by
  rw [h,h']
  simp
