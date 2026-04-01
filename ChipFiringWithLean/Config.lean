import ChipFiringWithLean.Basic
-- import Paperproof

set_option linter.unusedVariables false
set_option trace.split.failure true
set_option linter.unusedSectionVars false

open Multiset Finset

/-!
## Configurations and superstable configurations

Fix a vertex $q \in G.V$. A *configuration* (`Config G q`) is a nonnegative integer assignment
to the vertices `G.V \ {q}`, extended by zero at $q$. This corresponds to what
[Corry-Perkinson] calls a *nonnegative configuration* (Definition 2.9); we use "configuration"
to mean "nonnegative configuration" throughout this library.

A configuration $c$ is *superstable* if for every nonempty $S \subseteq G.V \setminus \{q\}$,
some vertex in $S$ has fewer chips than its out-degree into `G.V \ S`
([Corry-Perkinson], Definition 3.12). By `superstable_iff_q_reduced`, this is equivalent
to the associated divisor being $q$-reduced. A *maximal superstable* configuration is one
that is not dominated by any other superstable configuration.

The set `outdeg_S G q S v` counts edges from `v` to vertices outside `S`, and is the
relevant threshold for the superstability condition.
-/

/-- The set of vertices other than `q`: $\tilde{V} = G.V \setminus \{q\}$. -/
abbrev Vtilde {G : CFGraph} (q : G.V) : Finset G.V :=
  univ.filter (λ v => v ≠ q)

/-- A *configuration* on `G` with respect to distinguished vertex `q` is a nonnegative integer
assignment to all vertices, with the convention that `q` holds zero chips. This is what
[Corry-Perkinson] calls a *nonnegative configuration* (Definition 2.9). -/
structure Config (G : CFGraph) (q : G.V) where
  /-- Assignment of integers to vertices representing the number of chips at each vertex -/
  (vertex_degree : CFDiv G)
  /-- Fix vertex_degree q = 0 for convenience -/
  (q_zero : vertex_degree q = 0)
  /-- Proof that all vertices except q have non-negative values -/
  (non_negative : ∀ v : G.V, vertex_degree v ≥ 0)

/-- The degree of a configuration is the sum of all values except at q.
    deg(c) = ∑_{v ∈ G.V\{q}} c(v) -/
def config_degree {G : CFGraph} {q : G.V} (c : Config G q) : ℤ :=
  deg (c.vertex_degree)

/-- Convert a configuration `c` to a divisor of prescribed degree `d` by placing
`d - config_degree c` chips at `q`. -/
def toDiv {G : CFGraph} {q : G.V} (d : ℤ) (c : Config G q) : CFDiv G :=
  c.vertex_degree + (d - config_degree c) • (one_chip q)

/-- Two configurations are equal iff their `vertex_degree` functions agree. -/
lemma eq_config_iff_eq_vertex_degree {q : G.V} (c₁ c₂ : Config G q) :
  c₁ = c₂ ↔ c₁.vertex_degree = c₂.vertex_degree := by
  constructor
  · intro h_eq
    rw [h_eq]
  · intro h_eq
    obtain ⟨vd₁, _, _⟩ := c₁
    obtain ⟨vd₂, _, _⟩ := c₂
    simp only [Config.mk.injEq]
    funext v
    exact congrFun h_eq v

/-- Two configurations are equal iff their images under `toDiv d` agree. -/
lemma eq_config_iff_eq_div {q : G.V} (d : ℤ) (c₁ c₂ : Config G q) : c₁ = c₂ ↔ toDiv d c₁ = toDiv d c₂ := by
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

/-- Convert a configuration `c` to the $q$-effective divisor `toDiv d c`,
bundled with its proof of $q$-effectivity. -/
def to_qed {q : G.V} (d : ℤ) (c : Config G q) : q_eff_div G q :=
  {
    D := toDiv d c,
    h_eff := by
      intro v h_v
      dsimp [toDiv]
      simp [h_v]
      exact c.non_negative v
  }
/-- Convert a $q$-effective divisor to a configuration by zeroing out the chip count at `q`. -/
def toConfig {q : G.V} (D : q_eff_div G q) : Config G q := {
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

/-- The degree of a $q$-effective divisor equals its value at `q` plus the configuration degree. -/
def config_degree_div_degree {q : G.V} (D : q_eff_div G q) : deg D.D = D.D q + config_degree (toConfig D) := by
  simp only [config_degree, toConfig, map_sub, map_zsmul, deg_one_chip, smul_eq_mul, mul_one]
  ring

/-- `toConfig` is a left inverse of `to_qed`: converting a configuration to a $q$-effective
divisor and back recovers the original configuration. -/
lemma config_of_div_of_config (c : Config G q) (d : ℤ)  :
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

/-- `to_qed` is a left inverse of `toConfig` at the correct degree: converting a $q$-effective
divisor to a configuration and back via `toDiv (deg D.D)` recovers the original divisor. -/
lemma div_of_config_of_div (D : q_eff_div G q) :
  toDiv (deg D.D) (toConfig D) = D.D := by
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
    simp only [(toConfig D).q_zero, zero_add, one_chip, ite_true, mul_one]
    linarith [config_degree_div_degree D]

@[simp] lemma eval_toDiv_q {q : G.V} (d : ℤ) (c : Config G q) :
  toDiv d c q = d - config_degree c := by
  dsimp [toDiv]
  simp [c.q_zero]

@[simp] lemma eval_toDiv_ne_q {q v : G.V} (d : ℤ) (c : Config G q) (h_v : v ≠ q) :
  toDiv d c v = c.vertex_degree v := by
  dsimp [toDiv]
  simp [h_v]


/-- The divisor `toDiv d c` is effective iff `d ≥ config_degree c`, i.e. there are enough
chips at `q` to cover any debt. -/
lemma config_eff {q : G.V} (d : ℤ) (c : Config G q) : effective (toDiv d c) ↔ d ≥ config_degree c := by
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

instance : PartialOrder (Config G q) := {
  le := λ c₁ c₂ => c₁.vertex_degree ≤ c₂.vertex_degree,
  le_refl := by
    intro _
    simp,
  le_trans := by
    intro _ _ _ c1_le_c2 c2_le_c3
    exact le_trans c1_le_c2 c2_le_c3,
  le_antisymm := by
    intro c1 c2 h_le h_ge
    have h_eq := le_antisymm h_le h_ge
    exact (eq_config_iff_eq_vertex_degree c1 c2).mpr h_eq
}

/-- Two configurations are equal if one is pointwise bounded above by the other and they have
the same degree. -/
lemma config_eq_of_le_and_degree {q : G.V} {c1 c2 : Config G q} (h_le : c2 ≤ c1)
    (h_deg : config_degree c1 = config_degree c2) : c1 = c2 := by
  apply (eq_config_iff_eq_vertex_degree c1 c2).mpr
  dsimp [config_degree, deg] at h_deg
  have h_le' : ∀ v : G.V, c2.vertex_degree v ≤ c1.vertex_degree v := by
    intro v
    exact h_le v
  suffices ∀ v : G.V, c1.vertex_degree v = c2.vertex_degree v by
    funext v
    exact this v
  contrapose! h_deg with h_ne
  rcases h_ne with ⟨v, h_v_ne⟩
  have h_gt : c2.vertex_degree v < c1.vertex_degree v := by
    specialize h_le' v
    apply lt_of_le_of_ne h_le'
    contrapose! h_v_ne
    simp [h_v_ne]
  suffices config_degree c2 < config_degree c1 by
    exact ne_of_gt this
  dsimp [config_degree, deg]
  refine Finset.sum_lt_sum ?_ ?_
  · intro i _
    exact h_le' i
  · use v
    simp [h_gt]

/-- The out-degree of vertex `v` with respect to set `S`: the number of edges from `v` to
vertices outside `S`. Used to define the superstability condition. -/
def outdeg_S (G : CFGraph) (q : G.V) (S : Finset G.V) (v : G.V) : ℤ :=
  ∑ w ∈ (univ \ S), (num_edges G v w : ℤ)

/-- A configuration `c` is *superstable* if for every nonempty $S \subseteq G.V \setminus \{q\}$,
some vertex in $S$ has fewer chips than its out-degree into `G.V \ S`.
[Corry-Perkinson], Definition 3.12 -/
def superstable (G : CFGraph) (q : G.V) (c : Config G q) : Prop :=
  ∀ S ⊆  Vtilde q, S.Nonempty →
    ∃ v ∈ S, c.vertex_degree v < outdeg_S G q S v

/-- A configuration `c` is superstable iff `toDiv d c` is $q$-reduced (for any `d`).
[Corry-Perkinson], Remark 3.14 -/
lemma superstable_iff_q_reduced (G : CFGraph) (q : G.V) (d : ℤ) (c : Config G q) :
  superstable G q c ↔ q_reduced G q (toDiv d c) := by

  -- Little rewriting needed later
  have comp_eq (S : Finset G.V): univ \ S = Finset.filter (λ w => w ∉ S) univ := by
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
lemma q_reduced_superstable_correspondence (G : CFGraph) (q : G.V) (D : CFDiv G) :
  q_reduced G q D ↔ ∃ c : Config G q, superstable G q c ∧
  D = toDiv (deg D) c := by
  constructor
  . -- Forward direction (q_reduced → ∃ c, superstable ∧ D = c - δ_q)
    intro h_qred
    let D_qed : q_eff_div G q := {
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
def maximal_superstable (G : CFGraph) {q : G.V} (c : Config G q) : Prop :=
  superstable G q c ∧ ∀ c' : Config G q, superstable G q c' → c ≤ c' → c' = c


/-- Subtracting a chip at q from a superstable configuration gives an unwinnable divisor. -/
lemma helper_superstable_to_unwinnable {G : CFGraph} (h_conn : graph_connected G) (q : G.V) (c : Config G q) :
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


/-!
## Burn lists and Dhar's burning algorithm

A *burn list* for a configuration `c` is an ordered list of all vertices ending at `q`,
built by Dhar's burning algorithm: each vertex is added when its number of chips is less
than its out-degree into the remaining (unburned) vertices. The key property is that a
configuration is superstable if and only if a complete burn list (containing all vertices)
exists (`superstable_burn_list`).

The `burn_flow` function extracts an orientation from a burn list by directing each edge
toward the vertex that appears earlier in the list. This is used to construct the bijection
between maximal superstable configurations and acyclic orientations with unique source `q`
(see `Orientation.lean`).
-/


/-- Definition: A burn list for a configuration `c` is a list `[v_1, v_2, ..., v_n, q]`
  of distinct vertices ending at `q`, where the following condition holds at each vertex
  except `q`: if `S` is the set `G.V \ {v_1, ..., v_(n-1)}` (which contains `v_n`), then the
  out-degree of `v_n` with respect to `S` is greater than the number of chips at `v_n`. -/
def is_burn_list (G : CFGraph) {q : G.V} (c : Config G q) (L : List G.V) : Prop :=
  match L with
  | [] => False
  | [x] => (x = q)
  | v :: w :: rest =>
      outdeg_S G q (univ \ (w :: rest).toFinset) v > c.vertex_degree v
      -- v isn't in the set made out of w :: rest
      ∧ ¬ (w :: rest).contains v
      ∧ is_burn_list G c (w :: rest)

/-- Every burn list contains `q` (since the base case of a burn list is `[q]`). -/
lemma burn_list_contains_q (G : CFGraph) {q : G.V} (c : Config G q) (L : List G.V) (h_bl : is_burn_list G c L) :
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

/-- If `c` is superstable and a burn list `L` does not yet contain all vertices, it can be
extended by prepending a new vertex. This corresponds to the next edge burning in Dhar's
burning algorithm; superstability implies that the entire graph will burn. -/
lemma extend_burn_list (G : CFGraph) {q : G.V} (c : Config G q) (h_ss : superstable G q c) (L : List G.V) : is_burn_list G c L → (∃ v : G.V, ¬ L.contains v) → (∃ w : G.V, w ∉ L.toFinset ∧ is_burn_list G c (w :: L)) := by
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

/-- A bundled burn list: a list `L` of vertices together with a proof that it satisfies the
`is_burn_list` conditions for configuration `c`. -/
structure burn_list (G : CFGraph) {q : G.V} (c : Config G q) where
  (list : List G.V)
  (h_burn_list : is_burn_list G c list)

/-- For each `n < |G.V|`, there exists a burn list of size `n+1`. Inductive step for
`superstable_burn_list`. -/
lemma burn_list_helper (G : CFGraph) {q : G.V} (c : Config G q) (h_ss : superstable G q c) (n : ℕ) : (n < Finset.card (univ : Finset G.V))→ ∃ (L : List G.V), L.toFinset.card = n+1 ∧ is_burn_list G c L := by
  intro h_n_lt_card_V
  induction n with
  | zero =>
    use [q]
    constructor
    simp
    dsimp [is_burn_list]
  | succ n ih =>
    have ih_L : n < (univ : Finset G.V).card := by
      linarith
    apply ih at ih_L
    rcases ih_L with ⟨L, h_L_length, h_L_burn_list⟩
    have h_exists_v : ∃ v : G.V, ¬ L.contains v := by
      have h_card_L_le : L.toFinset.card < (univ : Finset G.V).card := by
        rw [← h_L_length] at h_n_lt_card_V
        linarith
      obtain ⟨v, -, h_v_not_in_L⟩ := Finset.exists_mem_notMem_of_card_lt_card h_card_L_le
      exact ⟨v, by simpa using h_v_not_in_L⟩
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

/-- A superstable configuration admits a complete burn list containing every vertex of `G`.
This is the key output of Dhar's burning algorithm: in a superstable configuration, the
whole graph burns. -/
lemma superstable_burn_list (G : CFGraph) {q : G.V} (c : Config G q) (h_ss : superstable G q c) : ∃ L : burn_list G c, ∀ v : G.V, v ∈ L.list := by
  have h_card_V : (univ : Finset G.V).card ≥ 1 := by
    have h_nonempty : Nonempty G.V := by infer_instance
    have h_card_pos : (univ : Finset G.V).card > 0 := Fintype.card_pos_iff.mpr h_nonempty
    linarith
  have : (univ : Finset G.V).card - 1 < (univ : Finset G.V).card := by
    simp
    -- Now show `Fintype.card G.V > 0`, so that the subtraction makes sense.
    apply Fintype.card_pos_iff.mpr
    infer_instance
  have h_burn_list := burn_list_helper G c h_ss ((univ : Finset G.V).card - 1) this
  rcases h_burn_list with ⟨L, h_L_length, h_L_burn_list⟩
  have h_L_card : L.toFinset.card = (univ : Finset G.V).card := by
    simp [h_L_length]
    apply Nat.sub_add_cancel
    exact h_card_V
  use burn_list.mk L h_L_burn_list
  have h_toFinset_eq : L.toFinset = (univ : Finset G.V) := by
    refine Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_
    simp [h_L_card]
  intro v
  have : v ∈ L.toFinset := by simp [h_toFinset_eq]
  simpa using this

-- The following lemmas establish the necessary properties of the orientation to be defined from the burn order.

/-- The orientation induced by a burn list: for each edge `(u, v)`, direct it from `u` to `v`
(i.e. assign nonzero flow) if `u` appears in the list and `v` appears before `u`. In other
words, the orientation indicates the direction of the spreading fire in Dhar's burning
algorithm. -/
def burn_flow {G : CFGraph} {q : G.V} {c : Config G q} (L : burn_list G c) : (G.V × G.V) → ℕ :=
  λ e => if (e.1 ∈ L.list) ∧ (L.list.idxOf e.2 < L.list.idxOf e.1) then num_edges G e.1 e.2 else 0

/-- The `burn_flow` of a complete burn list is a valid orientation: for every edge `{u, v}`,
exactly `num_edges G u v` units of flow are directed in one of the two directions. -/
lemma burn_flow_reverse {G : CFGraph} {q : G.V} {c : Config G q} (L : burn_list G c) (h_full : ∀ v : G.V, v ∈ L.list) : ∀ (u v : G.V), (burn_flow L ⟨u, v⟩) + (burn_flow L ⟨v, u⟩) = num_edges G u v := by
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

/-- The `burn_flow` of a complete burn list is directed: for every pair `(u, v)`, flow goes
in at most one direction. -/
lemma burn_flow_directed {G : CFGraph} {q : G.V} {c : Config G q} (L : burn_list G c) (h_full : ∀ v : G.V, v ∈ L.list) : ∀ (u v : G.V), burn_flow L ⟨u,v⟩ = 0 ∨ burn_flow L ⟨v,u⟩ = 0 := by
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

/-- For any non-`q` vertex `v` in a burn list, the in-flow into `v` exceeds the number of
chips at `v`. This is the key inequality used to construct the acyclic orientation from a
maximal superstable configuration. -/
lemma burnin_degree {G : CFGraph} {q : G.V} {c : Config G q} (L : burn_list G c) (v : G.V) (h_pres : v ∈ L.list) (h_ne : v ≠ q): ∑ (w : G.V), burn_flow L ⟨w,v⟩ > c.vertex_degree v := by
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
        suffices ∑ (w : G.V), burn_flow L ⟨w,v⟩ ≥ outdeg_S G q (univ \ (y :: rest').toFinset) v by
          linarith [this, h_bl.1]
        dsimp [burn_flow]
        have ind_v : L.list.idxOf v = 0 := by
          rw [h_vx,h]
          simp
        simp only [ind_v]
        have h_ineq := h_bl.1
        have h_above : ∀ (x : G.V), x ∈ L.list ∧ 0 < List.idxOf x L.list ↔ x ∈ rest := by
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
              rw [List.idxOf_cons_ne _ (Ne.symm h_neq)]
              simp
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
        have h_step : ∀ (w : G.V), burn_flow L ⟨w,v⟩ = burn_flow L' ⟨w,v⟩ := by
          have h_x_nin_rest: x ∉ rest := by
            have := L.h_burn_list
            rw [h] at this
            have := this.2.1
            rw [h']
            simp at this
            simp [this]
          intro w
          dsimp [burn_flow, L']
          rw [h]
          rw [List.idxOf_cons_ne _ (Ne.symm h_vx)]
          by_cases h_wx : w = x
          . -- Subcase: w = x
            rw [h_wx]
            have h0 : (x :: y :: rest').idxOf x = 0 := List.idxOf_cons_self
            rw [h0, if_neg (fun ⟨_, h⟩ => Nat.not_lt_zero _ h),
               if_neg (fun ⟨h_mem, _⟩ => (h' ▸ h_x_nin_rest) h_mem)]
          . -- Subcase: w ≠ x
            simp only [List.mem_cons, h_wx, false_or]
            rw [List.idxOf_cons_ne (y :: rest') (Ne.symm h_wx)]
            simp only [Nat.succ_lt_succ_iff]
        simp only [h_step]
        have h_ind := burnin_degree L' v h_v_in_L' h_ne
        exact h_ind
termination_by L.list.length
decreasing_by
  rw [h,h']
  simp
