import ChipFiringWithLean.Orientation
import ChipFiringWithLean.Rank
import Paperproof

set_option linter.unusedVariables false
set_option trace.split.failure true
set_option linter.unusedSectionVars false

open Multiset Finset Classical

-- Assume V is a finite type with decidable equality
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]


/-
# Helpers for Corollary 4.2.3 + Handshaking Theorem
-/

/-- Helper lemma: In a loopless graph, each edge has distinct endpoints -/
lemma edge_endpoints_distinct (G : CFGraph V) (e : V × V) (he : e ∈ G.edges) :
    e.1 ≠ e.2 := by
  by_contra eq_endpoints
  rcases e with ⟨u,v⟩
  have : u = v := eq_endpoints
  rw [this] at he
  exact G.loopless v he

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

/-- Helper lemma to rewrite (in-)degree in terms of edge counts from each direction.
This proof is quite clunky, and I suspect it can be simplified. -/
lemma degree_eq_total_flow : ∀ (S : Multiset (V × V)) (v : V), (∀ e ∈ S, e.1 ≠ e.2) →
  ∑ u : V, Multiset.card (Multiset.filter (fun e ↦ e = (v, u) ∨ e = (u, v)) S) = Multiset.card (S.filter (λ e => e.fst = v ∨ e.snd = v)) := by
  -- Induct on the multiset S
  intro S v h_loopless
  induction S using Multiset.induction_on with
  | empty =>
    simp only [Multiset.filter_zero, Multiset.card_zero, Finset.sum_const_zero]
  | cons e_head s_tail ih_s_tail =>
    -- Rewrite both sides using the head and tail
    simp only [Multiset.filter_cons, Multiset.card_add, sum_add_distrib]
    rw [ih_s_tail]
    -- Cancel the like terms in a + b = a + c
    suffices h : ∑ x : V, Multiset.card (if e_head = (v, x) ∨ e_head = (x, v) then {e_head} else 0) = Multiset.card (if e_head.1 = v ∨ e_head.2 = v then {e_head} else 0) by linarith

    by_cases h_head : (e_head.fst = v ∨ e_head.snd = v)
    · -- Case: e_head is incident to v
      simp only [if_pos h_head, Multiset.card_singleton]
      obtain ⟨e,f⟩ := e_head
      rcases h_head with h_left  | h_right
      -- Subcase: e = v
      have e_eq_v : e =v  := h_left
      have f_neq_v : f ≠ v := by
        contrapose! h_left
        simp
        rw [← h_left]
        exact h_loopless ⟨e,f⟩ (by simp)
      simp [e_eq_v, f_neq_v]
      -- Now only one term in this sum is nonzero
      have h (x:V): Multiset.card (if f = x then {(v, f)} else 0) = (if x = f then 1 else 0) := by
        by_cases h_x : x = f
        · simp [h_x]
        · simp [h_x]
          contrapose! h_x
          rw [h_x]
      simp [h]
      -- Subcase: f = v
      -- Similar argument
      have f_eq_v : f = v := h_right
      have e_neq_v : e ≠ v := by
        contrapose! h_right
        simp
        rw [← h_right]
        have := h_loopless ⟨e,f⟩ (by simp)
        intro h_bad
        rw [h_bad] at this
        apply absurd this
        simp

      simp [f_eq_v, e_neq_v]
      -- Now only one term in this sum is nonzero
      have h (x:V): Multiset.card (if e = x then {(e,v)} else 0) = (if x = e then 1 else 0) := by
        by_cases h_x : x = e
        · simp [h_x]
        · simp [h_x]
          contrapose! h_x
          rw [h_x]
      simp [h]
    · -- Case: e_head is not incident to v
      simp only [if_neg h_head]
      apply Finset.sum_eq_zero
      intro x _
      simp
      push_neg at h_head
      contrapose! h_head
      intro h'
      have h'': e_head ≠ ⟨v,x⟩ := by
        contrapose! h'
        simp [h']
      apply h_head at h''
      simp [h'']
    intro e
    specialize h_loopless e
    intro h_tail
    apply h_loopless
    simp [h_tail]

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


/-
# Helpers for Rank Degree Inequality used in RRG
-/

/-- Lemma: Dhar's algorithm produces a superstable configuration and chip count at q.
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
lemma helper_dhar_algorithm {G : CFGraph V} (h_conn : graph_connected G) (q : V) (D : CFDiv V) :
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

-- /-- Lemma: Dhar's algorithm produces negative k for unwinnable divisors
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



/-- Lemma: Given a graph G and a vertex q, there exists a maximal superstable divisor
    c' that is greater than or equal to any superstable divisor c. This is a key
    result from Corry & Perkinson's "Divisors and Sandpiles" (AMS, 2018) that is
    used in proving the Riemann-Roch theorem for graphs. -/
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
