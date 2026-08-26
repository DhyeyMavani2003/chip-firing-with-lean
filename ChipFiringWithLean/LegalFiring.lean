import ChipFiringWithLean.Basic

open Finset BigOperators

/-!
## Legal set firings

The basic vocabulary for firing a set of vertices, including the truncation
lemma used to decompose a firing script into nested legal firings.
-/

variable {G : CFGraph}








def indicator_script (G : CFGraph) (S : Finset G.V) : firing_script G :=
  fun v => if v ∈ S then 1 else 0

theorem set_firing_eq_add_prin_indicator_script (G : CFGraph) (D : CFDiv G)
    (S : Finset G.V) :
    set_firing G D S = D + prin G (indicator_script G S) := by
  classical
  funext v
  by_cases hv : v ∈ S
  · simp [set_firing, indicator_script, prin_apply, outdeg_S, hv]
    simp only [sub_mul, one_mul]
    rw [Finset.sum_sub_distrib]
    have hs : S.sum (fun x => (num_edges G v x : ℤ)) =
        (univ : Finset G.V).sum (fun x =>
          (if x ∈ S then 1 else 0) * (num_edges G v x : ℤ)) := by
      simpa using (Finset.sum_subset (s₁ := S) (s₂ := (univ : Finset G.V))
        (f := fun x => (if x ∈ S then 1 else 0) * (num_edges G v x : ℤ))
        (Finset.subset_univ S) (by
          intro x _ hx
          simp [hx]))
    rw [← hs]
    ring
  · simp [set_firing, indicator_script, prin_apply, outdeg_S, hv]

@[simp] theorem prin_const (G : CFGraph) (c : ℤ) :
    prin G (fun _ : G.V => c) = 0 := by
  funext v
  rw [prin_apply]
  simp

theorem set_firing_compl_set_firing (G : CFGraph) (D : CFDiv G) (S : Finset G.V) :
    set_firing G (set_firing G D S) Sᶜ = D := by
  classical
  rw [set_firing_eq_add_prin_indicator_script, set_firing_eq_add_prin_indicator_script]
  have hsum : indicator_script G S + indicator_script G Sᶜ =
      (fun _ : G.V => (1 : ℤ)) := by
    funext v
    by_cases hv : v ∈ S <;> simp [indicator_script, hv]
  rw [add_assoc, ← map_add, hsum, prin_const, add_zero]

theorem effective_add_prin_truncate (G : CFGraph) {D : CFDiv G}
    {σ : firing_script G} (hD : effective D)
    (hDσ : effective (D + prin G σ)) (c : ℤ) :
    effective (D + prin G (fun v => max (σ v - c) 0)) := by
  intro v
  have hnonneg : ∀ w : G.V, 0 ≤ max (σ w - c) 0 := fun w => le_max_right _ _
  have hge : ∀ w : G.V, σ w - c ≤ max (σ w - c) 0 := fun w => le_max_left _ _
  by_cases hv : σ v ≤ c
  · have hv' : max (σ v - c) 0 = 0 := max_eq_right (by omega)
    have hp : 0 ≤ prin G (fun w => max (σ w - c) 0) v := by
      rw [prin_apply]
      refine Finset.sum_nonneg fun u _ => ?_
      have : (0 : ℤ) ≤ max (σ u - c) 0 - max (σ v - c) 0 := by
        rw [hv']
        omega
      exact mul_nonneg this (Int.natCast_nonneg _)
    simp only [Pi.add_apply]
    have := hD v
    omega
  · have hv' : max (σ v - c) 0 = σ v - c := max_eq_left (by omega)
    have hp : prin G σ v ≤ prin G (fun w => max (σ w - c) 0) v := by
      rw [prin_apply, prin_apply]
      refine Finset.sum_le_sum fun u _ => ?_
      refine mul_le_mul_of_nonneg_right ?_ (Int.natCast_nonneg _)
      rw [hv']
      omega
    have hfinal := hDσ v
    have hstart := hD v
    change 0 ≤ D v + prin G σ v at hfinal
    change 0 ≤ D v + prin G (fun w => max (σ w - c) 0) v
    omega

def set_firing_chain (G : CFGraph) (D : CFDiv G) (S : ℕ → Finset G.V) :
    ℕ → CFDiv G
  | 0 => D
  | i + 1 => set_firing G (set_firing_chain G D S i) (S i)

@[simp] theorem set_firing_chain_zero (G : CFGraph) (D : CFDiv G)
    (S : ℕ → Finset G.V) : set_firing_chain G D S 0 = D := rfl

@[simp] theorem set_firing_chain_succ (G : CFGraph) (D : CFDiv G)
    (S : ℕ → Finset G.V) (i : ℕ) :
    set_firing_chain G D S (i + 1) = set_firing G (set_firing_chain G D S i) (S i) := rfl

theorem linear_equiv_set_firing_chain (G : CFGraph) (D : CFDiv G)
    (S : ℕ → Finset G.V) (i : ℕ) :
    linear_equiv G D (set_firing_chain G D S i) := by
  induction i with
  | zero => exact linear_equiv.refl G D
  | succ i ih =>
      rw [set_firing_chain_succ]
      apply linear_equiv.trans ih
      unfold linear_equiv
      rw [sub_eq_add_neg, set_firing_eq_add_prin_indicator_script]
      refine (principal_iff_eq_prin G _).mpr ⟨indicator_script G (S i), ?_⟩
      funext v
      simp [Pi.add_apply, add_comm]

theorem effective_set_firing_chain (G : CFGraph) {D : CFDiv G} (hD : effective D)
    {S : ℕ → Finset G.V} {k : ℕ}
    (hlegal : ∀ i, i < k → legal_set G (set_firing_chain G D S i) (S i)) :
    ∀ i, i ≤ k → effective (set_firing_chain G D S i) := by
  intro i
  induction i with
  | zero => intro _; simpa using hD
  | succ i ih =>
      intro hik
      rw [set_firing_chain_succ]
      exact effective_set_firing_of_legal_set G (ih (by omega)) (hlegal i (by omega))

theorem exists_nested_legal_chain_aux (h_conn : graph_connected G) (q : G.V)
    {D : CFDiv G} (hD : effective D) :
    ∃ (k : ℕ) (U : ℕ → Finset G.V),
      (∀ i, i < k → U i ⊆ Finset.univ.erase q) ∧
      (∀ i, i < k → (U i).Nonempty) ∧
      (∀ i j, i ≤ j → j < k → U i ⊆ U j) ∧
      (∀ i, i < k → legal_set G (set_firing_chain G D U i) (U i)) ∧
      q_reduced G q (set_firing_chain G D U k) := by
  classical
  -- The target of the chain: the `q`-reduced representative, which is effective
  -- because `D` is.
  obtain ⟨D', hequiv, hred⟩ := exists_q_reduced_representative h_conn q D
  have hD'eff : effective D' :=
    effective_of_winnable_and_q_reduced G q D' ⟨D, hD, hequiv.symm⟩ hred
  -- The firing script carrying `D` to `D'`, normalized to vanish at `q`.
  obtain ⟨x₀, hx₀⟩ := (principal_iff_eq_prin G (D' - D)).mp hequiv
  set x : firing_script G := fun v => x₀ v - x₀ q with hxdef
  have hxq : x q = 0 := by simp [hxdef]
  have hD'eq : D' = D + prin G x := by
    rw [hxdef, prin_sub_const]
    funext v
    have h := congrFun hx₀ v
    simp only [Pi.sub_apply] at h
    simp only [Pi.add_apply]
    omega
  have hDx : effective (D + prin G x) := by rw [← hD'eq]; exact hD'eff
  -- The reverse script takes `D'` back to `D`.
  have hrev : effective (D' + prin G (fun v => -x v)) := by
    have hneg : prin G (fun v => -x v) = -prin G x := by
      have hxx : (fun v => -x v) = -x := rfl
      rw [hxx, map_neg]
    rw [hneg, hD'eq]
    have : D + prin G x + -prin G x = D := by abel
    rw [this]; exact hD
  -- **The script is nonnegative**: its minimum is attained at `q`, because the
  -- bottom level set is legal for the `q`-reduced divisor `D'`.
  have hxnonneg : ∀ v : G.V, 0 ≤ x v := by
    by_contra hcon
    push Not at hcon
    obtain ⟨v₀, hv₀⟩ := hcon
    obtain ⟨m, -, hm⟩ :=
      Finset.exists_min_image (Finset.univ : Finset G.V) x ⟨q, Finset.mem_univ q⟩
    set W : Finset G.V := Finset.univ.filter (fun v => x v = x m) with hW
    have hmW : m ∈ W := by simp [hW]
    have hWq : q ∉ W := by
      simp only [hW, Finset.mem_filter, Finset.mem_univ, true_and]
      intro h
      have hmv := hm v₀ (Finset.mem_univ v₀)
      omega
    -- `W` is legal for `D'`: it is the first firing of the reverse chain.
    have hWlegal : legal_set G D' W := by
      have htr := effective_add_prin_truncate G hD'eff hrev (-(x m) - 1)
      have heq : (fun v => max ((fun w => -x w) v - (-(x m) - 1)) 0)
          = indicator_script (G := G) W := by
        funext v
        have hge : x m ≤ x v := hm v (Finset.mem_univ v)
        by_cases h : x v = x m
        · have hvW : v ∈ W := by simp [hW, h]
          show max (-x v - (-(x m) - 1)) 0 = indicator_script (G := G) W v
          rw [indicator_script, if_pos hvW]
          omega
        · have hvW : v ∉ W := by simp [hW, h]
          show max (-x v - (-(x m) - 1)) 0 = indicator_script (G := G) W v
          rw [indicator_script, if_neg hvW]
          omega
      rw [heq, ← set_firing_eq_add_prin_indicator_script] at htr
      intro u hu
      have hu' := htr u
      rw [set_firing_apply_of_mem G D' hu] at hu'
      omega
    obtain ⟨v, hvW, hlt⟩ :=
      hred.2 W (by
        intro v hvW
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro hveq
        exact hWq (hveq ▸ hvW)) ⟨m, hmW⟩
    have hge := hWlegal v hvW
    rw [outdeg_S_eq_sum_filter] at hge
    omega
  -- The top of the chain.
  obtain ⟨p, -, hp⟩ :=
    Finset.exists_max_image (Finset.univ : Finset G.V) x ⟨q, Finset.mem_univ q⟩
  set K : ℤ := x p with hK
  have hK0 : 0 ≤ K := by rw [hK, ← hxq]; exact hp q (Finset.mem_univ q)
  set k : ℕ := K.toNat with hk
  have hkK : (k : ℤ) = K := Int.toNat_of_nonneg hK0
  -- The level sets, fired from the top level downwards, i.e. increasing.
  set U : ℕ → Finset G.V := fun i => Finset.univ.filter (fun v => K - (i : ℤ) ≤ x v) with hU
  have hmemU : ∀ (i : ℕ) (v : G.V), v ∈ U i ↔ K - (i : ℤ) ≤ x v := by
    intro i v
    simp [hU]
  -- The chain of divisors is the truncation family of the script.
  have hchain : ∀ t : ℕ,
      set_firing_chain G D U t = D + prin G (fun v => max (x v - (K - (t : ℤ))) 0) := by
    intro t
    induction t with
    | zero =>
        have h0 : (fun v => max (x v - (K - ((0 : ℕ) : ℤ))) 0) = (0 : firing_script G) := by
          funext v
          have hpv := hp v (Finset.mem_univ v)
          show max (x v - (K - ((0 : ℕ) : ℤ))) 0 = 0
          push_cast
          omega
        rw [set_firing_chain_zero, h0, map_zero]
        simp
    | succ t ih =>
        have key : (fun v : G.V => max (x v - (K - ((t : ℤ) + 1))) 0)
            = (fun v : G.V => max (x v - (K - (t : ℤ))) 0) + indicator_script (G := G) (U t) := by
          funext v
          show max (x v - (K - ((t : ℤ) + 1))) 0
              = max (x v - (K - (t : ℤ))) 0 + indicator_script (G := G) (U t) v
          by_cases h : K - (t : ℤ) ≤ x v
          · rw [indicator_script, if_pos ((hmemU t v).mpr h)]
            omega
          · rw [indicator_script, if_neg (fun hc => h ((hmemU t v).mp hc))]
            omega
        rw [set_firing_chain_succ, ih, set_firing_eq_add_prin_indicator_script]
        push_cast
        rw [key, map_add]
        abel
  -- Effectivity of every divisor in the chain, by the truncation lemma.
  have heff : ∀ t : ℕ, effective (set_firing_chain G D U t) := by
    intro t
    rw [hchain]
    exact effective_add_prin_truncate G hD hDx _
  refine ⟨k, U, ?_, ?_, ?_, ?_, ?_⟩
  · -- the fired sets avoid `q`
    intro i hi v hv
    have hvx : K - (i : ℤ) ≤ x v := (hmemU i v).mp hv
    have hik : (i : ℤ) < K := by omega
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ v⟩
    intro hveq
    rw [hveq, hxq] at hvx
    omega
  · -- the fired sets are nonempty
    intro i _
    refine ⟨p, (hmemU i p).mpr ?_⟩
    have : K = x p := hK
    have : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
    omega
  · -- the fired sets are nested
    intro i j hij _ v hv
    have hvx : K - (i : ℤ) ≤ x v := (hmemU i v).mp hv
    refine (hmemU j v).mpr ?_
    have : (i : ℤ) ≤ (j : ℤ) := by exact_mod_cast hij
    omega
  · -- every step is legal
    intro i _ u hu
    have h := heff (i + 1) u
    rw [set_firing_chain_succ, set_firing_apply_of_mem G _ hu] at h
    omega
  · -- the chain ends at the `q`-reduced representative
    have hend : set_firing_chain G D U k = D' := by
      rw [hchain, hD'eq, hkK]
      congr 1
      congr 1
      funext v
      have := hxnonneg v
      show max (x v - (K - K)) 0 = x v
      omega
    rw [hend]
    exact hred

structure NestedLegalChain (G : CFGraph) (q : G.V) (D : CFDiv G) where
  length : ℕ
  sets : ℕ → Finset G.V
  avoids : ∀ i, i < length → q ∉ sets i
  nonempty : ∀ i, i < length → (sets i).Nonempty
  nested : ∀ i j, i ≤ j → j < length → sets i ⊆ sets j
  legal : ∀ i, i < length → legal_set G (set_firing_chain G D sets i) (sets i)
  reduced : q_reduced G q (set_firing_chain G D sets length)

theorem exists_nestedLegalChain {G : CFGraph} (h_conn : graph_connected G)
    (q : G.V) {D : CFDiv G} (hD : effective D) :
    Nonempty (NestedLegalChain G q D) := by
  obtain ⟨k, S, havoids, hnonempty, hnested, hlegal, hred⟩ :=
    exists_nested_legal_chain_aux h_conn q hD
  exact ⟨⟨k, S, (fun i hi => by
    intro hq
    have hq' := havoids i hi hq
    simp at hq'), hnonempty, hnested,
    hlegal, hred⟩⟩
