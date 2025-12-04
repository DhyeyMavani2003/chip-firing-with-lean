import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Order.Lemmas
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Order.WellFounded
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lemmas
import Mathlib.Data.List.Cycle
import ChipFiringWithLean.Basic
import ChipFiringWithLean.Config
import Paperproof
import Mathlib.Data.List.Defs

set_option linter.unusedVariables false
set_option trace.split.failure true
set_option linter.unusedSectionVars false

open Multiset Finset

-- Assume V is a finite type with decidable equality
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]

/-- An orientation of a graph assigns a direction to each edge.
    The consistent field ensures each undirected edge corresponds to exactly
    one directed edge in the orientation. -/
structure CFOrientation (G : CFGraph V) :=
  /-- The set of directed edges in the orientation -/
  (directed_edges : Multiset (V × V))
  /-- Preserves edge counts between vertex pairs -/
  (count_preserving : ∀ v w,
    Multiset.count (v, w) G.edges + Multiset.count (w, v) G.edges =
    Multiset.count (v, w) directed_edges + Multiset.count (w, v) directed_edges)
  /-- No bidirectional edges in the orientation -/
  (no_bidirectional : ∀ v w,
    Multiset.count (v, w) directed_edges = 0 ∨
    Multiset.count (w, v) directed_edges = 0)

/-- Number of edges directed into a vertex under an orientation -/
def indeg (G : CFGraph V) (O : CFOrientation G) (v : V) : ℕ :=
  Multiset.card (O.directed_edges.filter (λ e => e.snd = v))

/-- Number of edges directed out of a vertex under an orientation -/
def outdeg (G : CFGraph V) (O : CFOrientation G) (v : V) : ℕ :=
  Multiset.card (O.directed_edges.filter (λ e => e.fst = v))

/-- A vertex is a source if it has no incoming edges (indegree = 0) -/
def is_source (G : CFGraph V) (O : CFOrientation G) (v : V) : Bool :=
  indeg G O v = 0

/-- A vertex is a sink if it has no outgoing edges (outdegree = 0) -/
def is_sink (G : CFGraph V) (O : CFOrientation G) (v : V) : Bool :=
  outdeg G O v = 0

/-- Helper function to check if two consecutive vertices form a directed edge -/
def is_directed_edge (G : CFGraph V) (O : CFOrientation G) (u v : V) : Bool :=
  (u, v) ∈ O.directed_edges

/-- Helper function for safe list access -/
def list_get_safe {α : Type} (l : List α) (i : Nat) : Option α :=
  l.get? i

/-- A directed path in a graph under an orientation -/
structure DirectedPath (G : CFGraph V) (O : CFOrientation G) where
  /-- The sequence of vertices in the path -/
  vertices : List V
  /-- Path must not be empty (at least one vertex) -/
  non_empty : vertices.length > 0
  /-- Every consecutive pair forms a directed edge -/
  valid_edges : ∀ (i : Nat), i + 1 < vertices.length →
    match (vertices.get? i, vertices.get? (i + 1)) with
    | (some u, some v) => is_directed_edge G O u v = true
    | _ => False
  /-- All vertices in the path are distinct -/
  distinct_vertices : ∀ (i j : Nat), i < vertices.length → j < vertices.length → i ≠ j →
    match (vertices.get? i, vertices.get? j) with
    | (some u, some v) => u ≠ v
    | _ => True

/-- A directed cycle is a directed path whose first and last vertices coincide.
    Apart from the repetition of the first/last vertex, all other vertices in the cycle are distinct. -/
structure DirectedCycle (G : CFGraph V) (O : CFOrientation G) :=
  (vertices : List V)
  /-- Every consecutive pair of vertices forms a directed edge in the orientation. -/
  (valid_edges : ∀ (i : Nat), i + 1 < vertices.length →
    match (vertices.get? i, vertices.get? (i + 1)) with
    | (some u, some v) => is_directed_edge G O u v = true
    | _ => False)
  /-- The cycle condition: first vertex equals last, and at least one edge.
      Length > 1 means at least 2 vertices, e.g., [v, v] for a self-loop (1 edge). -/
  (cycle_condition : vertices.length > 1 ∧
    match (vertices.get? 0, vertices.get? (vertices.length - 1)) with
    | (some start_node, some end_node) => start_node = end_node
    | _ => False) -- Should not be hit if vertices.length > 1
  /-- All internal vertices (ignoring the last vertex which is the same as the first)
      are distinct from each other. This ensures there are no other repeated vertices
      besides the repetition at the end forming the cycle. -/
  (distinct_internal_vertices : ∀ (i j : Nat),
    i < vertices.length - 1 →
    j < vertices.length - 1 →
    i ≠ j →
    match (vertices.get? i, vertices.get? j) with
    | (some u, some v) => u ≠ v
    | _ => True)

/-- Check if there are edges in both directions between two vertices -/
def has_bidirectional_edges (G : CFGraph V) (O : CFOrientation G) (u v : V) : Prop :=
  ∃ e₁ e₂, e₁ ∈ O.directed_edges ∧ e₂ ∈ O.directed_edges ∧ e₁ = (u, v) ∧ e₂ = (v, u)

/-- All multiple edges between same vertices point in same direction -/
def consistent_edge_directions (G : CFGraph V) (O : CFOrientation G) : Prop :=
  ∀ u v : V, ¬has_bidirectional_edges G O u v

/-- An orientation is acyclic if it has no directed cycles and
    maintains consistent edge directions between vertices -/
def is_acyclic (G : CFGraph V) (O : CFOrientation G) : Prop :=
  consistent_edge_directions G O ∧
  ¬∃ (c : DirectedCycle G O), True

/-- The set of ancestors of a vertex v (nodes x such that there is a path x -> ... -> v) -/
noncomputable def ancestors (G : CFGraph V) (O : CFOrientation G) (v : V) : Finset V :=
  let R : V → V → Prop := fun a b => is_directed_edge G O a b = true
  open Classical in univ.filter (fun x => Relation.TransGen R x v)

/-- Measure for vertex_level termination: number of ancestors. -/
noncomputable def vertexLevelMeasure (G : CFGraph V) (O : CFOrientation G) (v : V) : Nat :=
  (ancestors G O v).card

/-- Axiom [TODO]: Path vertices are internally distinct -/
axiom path_vertices_internally_distinct_axiom
  (G : CFGraph V) (O : CFOrientation G) (path_verts : List V) :
  (∀ (i j : Nat),
    i < path_verts.length - 1 →
    j < path_verts.length - 1 →
    i ≠ j →
    match (path_verts.get? i, path_verts.get? j) with
    | (some u, some v) => u ≠ v
    | _ => True)

/-- Lemma: No self-loops in acyclic orientations -/
lemma not_trans_gen_self_of_acyclic (G : CFGraph V) (O : CFOrientation G) (h_acyclic : is_acyclic G O) (v_node : V) :
    ¬Relation.TransGen (fun a b => is_directed_edge G O a b = true) v_node v_node := by
  let R := fun a b => is_directed_edge G O a b = true

  have construct_path_from_trans_gen : ∀ {v_start v_end : V}, (h_trans : Relation.TransGen R v_start v_end) →
    ∃ (path_verts : List V), path_verts.length ≥ 2 ∧
                              path_verts.head? = some v_start ∧
                              path_verts.getLast? = some v_end ∧
                              List.Chain' R path_verts := by
    intro v_s v_e h_trans_gen_s_e
    refine Relation.TransGen.recOn (motive := fun y_target _h_trans_ignored => -- y_target is current end node from v_s
                                      ∃ (path_verts : List V), path_verts.length ≥ 2 ∧
                                                              path_verts.head? = some v_s ∧ -- Fixed start v_s
                                                              path_verts.getLast? = some y_target ∧ -- Current end y_target
                                                              List.Chain' R path_verts) h_trans_gen_s_e ?_ ?_
    · -- Base case for recOn: single (h_Rxy : R x y)
      -- Parameters provided by recOn: x (fixed as v_s), y_node, h_R_x_y
      -- Here y_node is the target for the motive.
      intro y_node_base h_R_vs_ynode_base -- x is v_s (implicit), y_node_base is the 'y_target'
      use [v_s, y_node_base] -- Path from v_s to y_node_base
      refine' ⟨by simp, by simp, by simp, _⟩
      simp only [List.chain'_cons, List.chain'_singleton, and_true]
      exact h_R_vs_ynode_base -- R v_s y_node_base
    · -- Inductive step for recOn: tail (h_trans_x_mid : TransGen R x mid) (h_R_mid_z : R mid z) (ih_x_mid : motive x mid h_trans_x_mid)
      -- Parameters: x (fixed as v_s), mid, z, h_trans_x_mid (now TransGen R v_s mid), h_R_mid_z, ih_x_mid (now motive mid h_trans_v_s_mid)
      intro mid_node_ind z_node_ind h_trans_vs_mid h_R_mid_z ih_vs_mid
      obtain ⟨path_vsm, h_len_ge_2_vsm, h_head_eq_vs, h_last_eq_mid, h_chain'_vsm⟩ := ih_vs_mid
      use path_vsm ++ [z_node_ind]
      constructor
      ·
        simp only [List.length_append, List.length_singleton]
        apply Nat.le_trans h_len_ge_2_vsm (Nat.le_add_right _ 1)
      · constructor
        ·
          have h_path_vsm_ne_nil : path_vsm ≠ [] := List.ne_nil_of_length_pos (by linarith only [h_len_ge_2_vsm])
          simp only [List.head?_append, h_path_vsm_ne_nil, h_head_eq_vs, List.head?_cons, List.head?_nil, Option.some_orElse]
          rfl
        · constructor
          ·
            simp only [List.getLast?_append, List.getLast?_cons, List.getLast?_nil, Option.some_orElse]
            rfl -- Should be `some z_node_ind = some z_node_ind` by now
          ·
            -- Prove List.Chain' R (path_vsm ++ [z_node_ind])
            simp only [List.chain'_append, h_chain'_vsm, List.chain'_singleton, and_true]
            constructor
            · trivial
            constructor
            · trivial
            intros x hx y hy
            -- hx : path_vsm.getLast? = some x, h_last_eq_mid : path_vsm.getLast? = some mid_node_ind
            have hx' := hx.symm.trans h_last_eq_mid
            have eqx : x = mid_node_ind := Option.some.inj hx'
            subst eqx
            -- hy : y ∈ [z_node_ind].head?
            rw [Option.mem_def] at hy
            have eqy : y = z_node_ind := Option.some.inj hy.symm
            subst eqy
            exact h_R_mid_z


  intro h_trans_gen_v_v
  obtain ⟨path_verts, hv_path_verts_length_ge_2, hv_path_verts_head_eq_v_node,
            hv_path_verts_last_eq_v_node, h_path_verts_chain'_R⟩ := construct_path_from_trans_gen h_trans_gen_v_v

  have h_path_len_gt_1 : path_verts.length > 1 := Nat.lt_of_succ_le hv_path_verts_length_ge_2

  let dc : DirectedCycle G O := {
    vertices := path_verts,
    valid_edges := by
      intros i hi
      have hi' : i < path_verts.length := Nat.lt_of_succ_lt hi
      have hi1' : i + 1 < path_verts.length := hi
      rw [List.get?_eq_get hi', List.get?_eq_get hi1']
      exact (List.chain'_iff_get.mp h_path_verts_chain'_R) i (Nat.lt_pred_of_succ_lt hi)
    cycle_condition := by
      constructor
      · exact h_path_len_gt_1
      · cases h0_get : path_verts.get? 0;
        case none =>
          have h_path_is_nil : path_verts = [] := by
            cases path_verts with
            | nil => rfl
            | cons hd tl =>
              simp only [List.get?] at h0_get -- h0_get is now `some hd = none`
              exact (Option.noConfusion h0_get) -- Derives False from `some hd = none`
          rw [h_path_is_nil] at h_path_len_gt_1
          simp at h_path_len_gt_1 -- Contradiction: 0 > 1, proves False for this branch
        case some v0 =>
          cases h1_get : path_verts.get? (path_verts.length - 1);
          case none => -- path_verts.get? (path_verts.length - 1) = none
            exfalso
            rw [List.get?_eq_none] at h1_get -- h1_get is ¬ (path_verts.length - 1 < path_verts.length)
            have h_lt : path_verts.length - 1 < path_verts.length := by
              apply Nat.sub_lt_of_pos_le -- Proves n - k < n if 0 < k and k <= n
              · exact Nat.zero_lt_one -- k=1, 0 < 1
              · linarith [h_path_len_gt_1] -- path_verts.length > 1 implies 1 <= path_verts.length
            linarith [h_lt, h1_get] -- Should now find contradiction from (L-1 < L) and not(L-1 < L)
          case some v1 =>
            have ne_nil : path_verts ≠ [] := by intro H; rw[H] at h_path_len_gt_1; simp at h_path_len_gt_1
            have eq_v0 : v0 = v_node := by
              have h_head_eq_get_zero : path_verts.head? = path_verts.get? 0 := by
                cases path_verts with
                | nil => exfalso; exact ne_nil rfl
                | cons hd tl =>
                  simp only [List.head?, List.get?] -- head? (hd::tl) = some hd; get? (hd::tl) 0 = some hd
              rw [h_head_eq_get_zero] at hv_path_verts_head_eq_v_node
              rw [h0_get] at hv_path_verts_head_eq_v_node
              exact Option.some.inj hv_path_verts_head_eq_v_node
            have eq_v1 : v1 = v_node := by
              have h_last_eq_get_len_sub_one : path_verts.getLast? = path_verts.get? (path_verts.length - 1) :=
                (List.getLast?_eq_getElem? path_verts).trans ((List.get?_eq_getElem? path_verts (path_verts.length - 1)).symm)
              rw [h_last_eq_get_len_sub_one] at hv_path_verts_last_eq_v_node
              rw [h1_get] at hv_path_verts_last_eq_v_node
              exact Option.some.inj hv_path_verts_last_eq_v_node
            rw [eq_v0, eq_v1]
    distinct_internal_vertices := path_vertices_internally_distinct_axiom G O path_verts,
  };
  exact h_acyclic.2 (Exists.intro dc (by trivial));

/-- Key lemma for vertex_level termination -/
lemma ancestors_card_lt_of_pred_of_acyclic
    (G : CFGraph V) (O : CFOrientation G) (h_acyclic : is_acyclic G O)
    {u v_call : V} (u_is_pred_of_v_call : is_directed_edge G O u v_call = true) :
    vertexLevelMeasure G O u < vertexLevelMeasure G O v_call := by
  let R := fun a b => is_directed_edge G O a b = true
  apply Finset.card_lt_card
  -- Goal: ancestors G O u ⊂ ancestors G O v_call
  apply Finset.ssubset_def.mpr
  constructor
  · -- 1. ancestors G O u ⊆ ancestors G O v_call
    intros x hx_mem_anc_u
    simp only [ancestors, Finset.mem_filter, Finset.mem_univ, true_and] at hx_mem_anc_u ⊢
    exact Relation.TransGen.trans hx_mem_anc_u (Relation.TransGen.single u_is_pred_of_v_call)
  · -- 2. ¬ (ancestors G O v_call ⊆ ancestors G O u)
    --    This is equiv to ∃ k, k ∈ (ancestors G O v_call) ∧ k ∉ (ancestors G O u)
    --    We pick k = u.
    intro h_contra_subset_rev -- Assume for contradiction: ancestors G O v_call ⊆ ancestors G O u
    have u_in_anc_v_call : u ∈ ancestors G O v_call := by {
      simp only [ancestors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Relation.TransGen.single u_is_pred_of_v_call
    }
    have u_in_anc_u_from_contra : u ∈ ancestors G O u := h_contra_subset_rev u_in_anc_v_call
    have u_not_in_anc_u_from_acyclic : u ∉ ancestors G O u := by {
      simp only [ancestors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact not_trans_gen_self_of_acyclic G O h_acyclic u
    }
    exact u_not_in_anc_u_from_acyclic u_in_anc_u_from_contra

/-- The level of a vertex is its position in the topological ordering -/
noncomputable def vertex_level (G : CFGraph V) (O : CFOrientation G) (h_acyclic : is_acyclic G O) : V → Nat :=
  let R_measure_lt (y x : V) : Prop := vertexLevelMeasure G O y < vertexLevelMeasure G O x
  have wf_R_measure_lt : WellFounded R_measure_lt := -- Proof that the relation is well-founded
    (InvImage.wf (vertexLevelMeasure G O) Nat.lt_wfRel.wf) -- Corrected to Nat.lt_wfRel.wf
  WellFounded.fix wf_R_measure_lt
    (fun (v : V) (recursive_call_handler : Π (u_rec : V), R_measure_lt u_rec v → Nat) =>
      let predecessors := univ.filter (fun u_filter_pred => is_directed_edge G O u_filter_pred v = true)
      predecessors.attach.sup
        (fun (u_attached : {x // x ∈ predecessors}) =>
          let u_val := u_attached.val
          let proof_u_in_predecessors := u_attached.property
          have edge_proof : is_directed_edge G O u_val v = true :=
            (Finset.mem_filter.mp proof_u_in_predecessors).2
          recursive_call_handler u_val (ancestors_card_lt_of_pred_of_acyclic G O h_acyclic edge_proof) + 1
        )
    )

/-- Vertices at a given level in the orientation -/
noncomputable def vertices_at_level (G : CFGraph V) (O : CFOrientation G) (h_acyclic : is_acyclic G O) (l : ℕ) : Finset V :=
  univ.filter (λ v => vertex_level G O h_acyclic v = l)


/-- Vertices that are not sources must have at least one incoming edge. -/
lemma indeg_ge_one_of_not_source (G : CFGraph V) (O : CFOrientation G) (v : V) :
    ¬ is_source G O v → indeg G O v ≥ 1 := by
  intro h_not_source -- h_not_source : is_source G O v = false
  unfold is_source at h_not_source -- h_not_source : (decide (indeg G O v = 0)) = false
  apply Nat.one_le_iff_ne_zero.mpr -- Goal is indeg G O v ≠ 0
  intro h_eq_zero -- Assume indeg G O v = 0
  have h_decide_true : decide (indeg G O v = 0) = true := by
    rw [h_eq_zero]
    exact decide_eq_true rfl
  rw [h_decide_true] at h_not_source
  simp at h_not_source

/-- For vertices that are not sources, indegree - 1 is non-negative. -/
lemma indeg_minus_one_nonneg_of_not_source (G : CFGraph V) (O : CFOrientation G) (v : V) :
    ¬ is_source G O v → 0 ≤ (indeg G O v : ℤ) - 1 := by
  intro h_not_source
  have h_indeg_ge_1 : indeg G O v ≥ 1 := indeg_ge_one_of_not_source G O v h_not_source
  apply Int.sub_nonneg_of_le
  exact Nat.cast_le.mpr h_indeg_ge_1

/-- Configuration associated with a source vertex q under orientation O.
    Requires O to be acyclic and q to be the unique source.
    For each vertex v ≠ q, assigns indegree(v) - 1 chips. Assumes q is the unique source. -/
def config_of_source {G : CFGraph V} {O : CFOrientation G} {q : V}
    (h_acyclic : is_acyclic G O) (h_unique_source : ∀ w, is_source G O w → w = q) : Config V q :=
  { vertex_degree := λ v => if v = q then 0 else (indeg G O v : ℤ) - 1,
    non_negative_except_q := λ v hv => by
      simp [vertex_degree]
      split_ifs with h_eq
      · contradiction
      · have h_not_source : ¬ is_source G O v := by
          intro hs_v
          exact hv (h_unique_source v hs_v)
        exact indeg_minus_one_nonneg_of_not_source G O v h_not_source
  }

/-- The divisor associated with an orientation assigns indegree - 1 to each vertex -/
def divisor_of_orientation (G : CFGraph V) (O : CFOrientation G) : CFDiv V :=
  λ v => indeg G O v - 1

/-- The canonical divisor assigns degree - 2 to each vertex.
    This is independent of orientation and equals D(O) + D(reverse(O)) -/
def canonical_divisor (G : CFGraph V) : CFDiv V :=
  λ v => (vertex_degree G v) - 2

/-- Auxillary Lemma: Double canonical difference is identity -/
lemma canonical_double_diff (G : CFGraph V) (D : CFDiv V) :
  (λ v => canonical_divisor G v - (canonical_divisor G v - D v)) = D := by
  funext v; simp

/- Helper: Definition of reversing an orientation -/
def CFOrientation.reverse (G : CFGraph V) (O : CFOrientation G) : CFOrientation G where
  directed_edges := O.directed_edges.map Prod.swap -- Use Prod.swap directly
  count_preserving v w := by
    rw [O.count_preserving v w]

    have h_vw_rev_eq_wv_orig :
        Multiset.count (v,w) (O.directed_edges.map Prod.swap) = Multiset.count (w,v) O.directed_edges := by
      rw [Multiset.count_map (f := Prod.swap)]
      rw [Multiset.count_eq_card_filter_eq] -- Or Multiset.count, Multiset.countP_eq_card_filter
      apply congr_arg Multiset.card
      ext e
      simp only [Multiset.mem_filter, and_congr_left_iff, Prod.ext_iff, Prod.fst_swap, Prod.snd_swap, eq_comm, and_comm]

    have h_wv_rev_eq_vw_orig :
        Multiset.count (w,v) (O.directed_edges.map Prod.swap) = Multiset.count (v,w) O.directed_edges := by
      rw [Multiset.count_map (f := Prod.swap)]
      rw [Multiset.count_eq_card_filter_eq]
      apply congr_arg Multiset.card
      ext e
      simp only [Multiset.mem_filter, and_congr_left_iff, Prod.ext_iff, Prod.fst_swap, Prod.snd_swap, eq_comm, and_comm]

    conv_rhs =>
      congr
      · change Multiset.count (v,w) (O.directed_edges.map Prod.swap)
        rw [h_vw_rev_eq_wv_orig]
      · change Multiset.count (w,v) (O.directed_edges.map Prod.swap)
        rw [h_wv_rev_eq_vw_orig]

    rw [add_comm (Multiset.count (w,v) O.directed_edges)]
  no_bidirectional v w := by -- The `directed_edges` for this proof is O.directed_edges.map Prod.swap
    cases O.no_bidirectional v w with
    | inl h_vw_O_zero => -- Multiset.count (v, w) O.directed_edges = 0
      apply Or.inr
      rw [Multiset.count_eq_zero]
      intro h_wv_mem_rev_contra
      have h_vw_mem_O_derived : (v,w) ∈ O.directed_edges := by
        obtain ⟨p, h_p_mem_O, h_swap_p_eq_wv⟩ := Multiset.mem_map.mp h_wv_mem_rev_contra
        have h_p_is_vw : p = (v,w) := by { apply Prod.ext; exact (Prod.mk.inj h_swap_p_eq_wv).2; exact (Prod.mk.inj h_swap_p_eq_wv).1 }
        rwa [h_p_is_vw] at h_p_mem_O
      exact (Multiset.count_eq_zero.mp h_vw_O_zero) h_vw_mem_O_derived
    | inr h_wv_O_zero => -- Multiset.count (w, v) O.directed_edges = 0
      apply Or.inl
      rw [Multiset.count_eq_zero]
      intro h_vw_mem_rev_contra
      have h_wv_mem_O_derived : (w,v) ∈ O.directed_edges := by
        obtain ⟨p, h_p_mem_O, h_swap_p_eq_vw⟩ := Multiset.mem_map.mp h_vw_mem_rev_contra
        have h_p_is_wv : p = (w,v) := by { apply Prod.ext; exact (Prod.mk.inj h_swap_p_eq_vw).2; exact (Prod.mk.inj h_swap_p_eq_vw).1 }
        rwa [h_p_is_wv] at h_p_mem_O
      exact (Multiset.count_eq_zero.mp h_wv_O_zero) h_wv_mem_O_derived

/- Helper: indegree in reversed orientation equals outdegree in original -/
lemma indeg_reverse_eq_outdeg (G : CFGraph V) (O : CFOrientation G) (v : V) :
  indeg G (O.reverse G) v = outdeg G O v := by
  classical
  simp only [indeg, outdeg]
  rw [← Multiset.countP_eq_card_filter, ← Multiset.countP_eq_card_filter]
  let O_rev_edges_def : (CFOrientation.reverse G O).directed_edges = O.directed_edges.map Prod.swap := by rfl
  conv_lhs => rw [O_rev_edges_def]
  rw [Multiset.countP_map]
  simp only [Function.comp_apply, Prod.snd_swap]
  simp only [Multiset.countP_eq_card_filter]

/- Helper: If an orientation is acyclic, its reverse is also acyclic -/
lemma is_acyclic_reverse_of_is_acyclic (G : CFGraph V) (O : CFOrientation G)
    (h_acyclic : is_acyclic G O) :
  is_acyclic G (O.reverse G) := by
  constructor
  · -- consistent_edge_directions for O.reverse
    intro u v h_bidir_rev -- h_bidir_rev : has_bidirectional_edges G (O.reverse G) u v
    let O_rev := O.reverse G;
    obtain ⟨e₁, e₂, he₁_mem_rev, he₂_mem_rev, he₁_eq_uv, he₂_eq_vu⟩ := h_bidir_rev;

    have h_uv_mem_rev : (u,v) ∈ O_rev.directed_edges := by { rw [← he₁_eq_uv]; exact he₁_mem_rev };
    have h_vu_mem_rev : (v,u) ∈ O_rev.directed_edges := by { rw [← he₂_eq_vu]; exact he₂_mem_rev };

    have count_uv_rev_pos : Multiset.count (u,v) O_rev.directed_edges > 0 :=
      Multiset.count_pos.mpr h_uv_mem_rev;
    have count_vu_rev_pos : Multiset.count (v,u) O_rev.directed_edges > 0 :=
      Multiset.count_pos.mpr h_vu_mem_rev;

    cases O_rev.no_bidirectional u v with
    | inl h_uv_rev_zero => -- Multiset.count (u,v) O_rev.directed_edges = 0
      exact Nat.ne_of_gt count_uv_rev_pos h_uv_rev_zero;
    | inr h_vu_rev_zero => -- Multiset.count (v,u) O_rev.directed_edges = 0
      exact Nat.ne_of_gt count_vu_rev_pos h_vu_rev_zero;

  · -- No directed cycles in O.reverse
    rintro ⟨c_rev_inst, _⟩ -- c_rev_inst : DirectedCycle G (O.reverse G)
    apply h_acyclic.2; -- Need to show ∃ (c : DirectedCycle G O), True
    let O_rev := O.reverse G;
    let c_rev_verts := c_rev_inst.vertices;
    let c_orig_verts := c_rev_verts.reverse;

    use {
      vertices := c_orig_verts,
      valid_edges := by {
        intro i hi_idx_bound_orig;
        let L_orig := c_orig_verts.length;
        have h_L_orig_gt_one : L_orig > 1 := by { dsimp [L_orig, c_orig_verts]; rw [List.length_reverse]; exact c_rev_inst.cycle_condition.1 };
        have h_i_lt_L : i < L_orig := Nat.lt_of_succ_lt hi_idx_bound_orig;
        have h_i_succ_lt_L : i + 1 < L_orig := hi_idx_bound_orig;

        simp only [List.get?_eq_get h_i_lt_L, List.get?_eq_get h_i_succ_lt_L];
        -- Goal is now: is_directed_edge G O (c_orig_verts[i]) (c_orig_verts[i+1])

        let u_orig := c_orig_verts[i];
        let v_orig := c_orig_verts[i+1];

        let L_rev := c_rev_verts.length;
        have h_L_rev_eq_L_orig : L_rev = L_orig := by { simp [L_orig, c_orig_verts, List.length_reverse] };
        rw [←h_L_rev_eq_L_orig] at h_i_lt_L h_i_succ_lt_L h_L_orig_gt_one;

        let k_rev := L_rev - 1 - (i+1); -- This is index in c_rev_verts for v_orig
        let k_rev_plus_1 := L_rev - 1 - i; -- This is index in c_rev_verts for u_orig

        have h_k_rev_plus_1_lt_L_rev : k_rev_plus_1 < L_rev := by {
          dsimp [k_rev_plus_1]; -- Goal: (L_rev - 1) - i < L_rev
          apply Nat.lt_of_le_of_lt (Nat.sub_le (L_rev-1) i);
          exact (Nat.pred_lt_self (Nat.zero_lt_one.trans h_L_orig_gt_one)); -- L_rev-1 < L_rev because L_rev > 0
        };
        have h_k_rev_lt_k_rev_plus_1 : k_rev < k_rev_plus_1 := by {
          dsimp [k_rev, k_rev_plus_1]; -- Goal: L_rev - 1 - (i + 1) < L_rev - 1 - i
          let X_minus_i := (L_rev - 1) - i;
          have h_X_minus_i_pos : 0 < X_minus_i := by {
            apply Nat.sub_pos_of_lt;
            exact (Nat.lt_pred_iff_succ_lt.mpr h_i_succ_lt_L); -- i.succ < L_rev implies i < L_rev.pred
          };
          rw [Nat.sub_succ (L_rev-1) i]; -- LHS (L_rev-1)-(i+1) becomes (L_rev-1-i)-1
                                        -- Goal is (L_rev-1-i)-1 < (L_rev-1-i)
          exact Nat.pred_lt_self h_X_minus_i_pos;
        };
        have h_k_rev_lt_L_rev : k_rev < L_rev := Nat.lt_trans h_k_rev_lt_k_rev_plus_1 h_k_rev_plus_1_lt_L_rev;

        have h_bound_for_c_rev_valid_edges : k_rev + 1 < L_rev := by {
          dsimp [k_rev]; -- Goal is (L_rev - 1 - (i+1)) + 1 < L_rev
          linarith [h_i_succ_lt_L, h_L_orig_gt_one];
        };

        have h_val_edge_proof_term := c_rev_inst.valid_edges k_rev h_bound_for_c_rev_valid_edges;
        simp only [List.get?_eq_get h_k_rev_lt_L_rev, List.get?_eq_get h_bound_for_c_rev_valid_edges] at h_val_edge_proof_term;
        have h_krev_succ_eq_krev_plus_1 : k_rev + 1 = k_rev_plus_1 := by {
          dsimp [k_rev, k_rev_plus_1]; -- (L_rev - 1 - (i+1)) + 1 = L_rev - 1 - i
          let X_minus_i := (L_rev - 1) - i;
          have h_X_minus_i_pos : 0 < X_minus_i := by {
            apply Nat.sub_pos_of_lt;
            exact (Nat.lt_pred_iff_succ_lt.mpr h_i_succ_lt_L);
          };
          rw [Nat.sub_succ (L_rev-1) i]; -- LHS's (L_rev-1)-(i+1) part becomes (L_rev-1-i)-1. So LHS is ((L_rev-1-i)-1) + 1
                                        -- Goal is ((L_rev-1-i)-1) + 1 = (L_rev-1-i)
          exact Nat.succ_pred_eq_of_pos h_X_minus_i_pos;
        };
        simp only [h_krev_succ_eq_krev_plus_1] at h_val_edge_proof_term;
        have h_val_edge_rev : is_directed_edge G O_rev (c_rev_verts[k_rev]) (c_rev_verts[k_rev_plus_1]) = true := h_val_edge_proof_term;

        have h_target_edge_mem : (c_rev_verts[k_rev], c_rev_verts[k_rev_plus_1]) ∈ O_rev.directed_edges :=
          of_decide_eq_true h_val_edge_rev;
        obtain ⟨edge_in_O, h_edge_in_O_mem, h_swap_eq⟩ := Multiset.mem_map.mp h_target_edge_mem;

        have h_u_orig_maps : u_orig = c_rev_verts[L_rev - 1 - i] := by {
          simp only [u_orig, c_orig_verts, List.getElem_reverse];
        };
        have h_v_orig_maps : v_orig = c_rev_verts[L_rev - 1 - (i+1)] := by {
           simp only [v_orig, c_orig_verts, List.getElem_reverse];
        };

        have h_pair_eq : (c_rev_verts[k_rev], c_rev_verts[k_rev_plus_1]) = (v_orig, u_orig) := by {
          apply Prod.ext_iff.mpr;
          constructor;
          · -- Goal: c_rev_verts[k_rev] = v_orig
            -- k_rev is L_rev - 1 - (i+1)
            -- h_v_orig_maps is v_orig = c_rev_verts[L_rev - 1 - (i+1)]
            exact (Eq.symm h_v_orig_maps);
          · -- Goal: c_rev_verts[k_rev_plus_1] = u_orig
            -- k_rev_plus_1 is L_rev - 1 - i
            -- h_u_orig_maps is u_orig = c_rev_verts[L_rev - 1 - i]
            exact (Eq.symm h_u_orig_maps);
        };
        rw [h_pair_eq] at h_swap_eq;
        have h_edge_eq_orig_pair : edge_in_O = (u_orig, v_orig) := Prod.swap_inj.mp h_swap_eq;
        rw [h_edge_eq_orig_pair] at h_edge_in_O_mem;
        simp [is_directed_edge, h_edge_in_O_mem];
      },
      cycle_condition := by {
        constructor;
        · -- Length part
          dsimp [c_orig_verts]; rw [List.length_reverse];
          exact c_rev_inst.cycle_condition.1;
        · -- Endpoints part
          let L_orig := c_orig_verts.length;
          have h_L_orig_gt_one : L_orig > 1 := by { dsimp [L_orig, c_orig_verts]; rw [List.length_reverse]; exact c_rev_inst.cycle_condition.1; };
          have h_L_orig_pos : L_orig > 0 := by linarith [h_L_orig_gt_one];
          have h_idx0_lt_L_orig_get : 0 < L_orig := h_L_orig_pos;
          have h_idxL_1_lt_L_orig_get : L_orig - 1 < L_orig := Nat.sub_lt h_L_orig_pos Nat.one_pos;

          simp only [List.get?_eq_get h_idx0_lt_L_orig_get, List.get?_eq_get h_idxL_1_lt_L_orig_get];
          -- Goal is now: c_orig_verts[0] = c_orig_verts[L_orig - 1]

          let hc_cond_rev := c_rev_inst.cycle_condition;
          let h_L_rev_gt_1 := hc_cond_rev.1; -- This is c_rev_verts.length > 1
          let L_rev := c_rev_verts.length;
          have h0_lt_Lrev : 0 < L_rev := Nat.lt_trans Nat.zero_lt_one h_L_rev_gt_1;
          have hLrev_minus_1_lt_Lrev : L_rev - 1 < L_rev := Nat.pred_lt_of_lt h_L_rev_gt_1;

          have h_eq_rev_direct : (c_rev_verts.get ⟨0, h0_lt_Lrev⟩) = (c_rev_verts.get ⟨L_rev - 1, hLrev_minus_1_lt_Lrev⟩) := by {
            rcases hc_cond_rev with ⟨_, h_match_prop⟩; -- _ is h_L_rev_gt_1, already captured
            simp only [List.get?_eq_get h0_lt_Lrev, List.get?_eq_get hLrev_minus_1_lt_Lrev] at h_match_prop;
            exact h_match_prop;
          };
          have h_L_rev_eq_L_orig : c_rev_verts.length = c_orig_verts.length := (List.length_reverse c_rev_verts).symm;
          dsimp only [c_orig_verts]; simp only [List.get_eq_getElem, List.getElem_reverse, List.length_reverse, L_orig, L_rev, Nat.sub_zero, Nat.sub_sub, Nat.sub_self, Nat.add_one_sub_one, h_L_rev_eq_L_orig] at h_idx0_lt_L_orig_get h_idxL_1_lt_L_orig_get h_eq_rev_direct ⊢;
          rw [eq_comm]; exact h_eq_rev_direct;
      },
      distinct_internal_vertices := by {
        intro i j hi_bound_orig hj_bound_orig h_i_ne_j;
        let L_orig := c_orig_verts.length;
        have h_L_orig_gt_one : L_orig > 1 := by { dsimp [L_orig, c_orig_verts]; rw [List.length_reverse]; exact c_rev_inst.cycle_condition.1 };
        have h_i_lt_L_minus_1 : i < L_orig - 1 := hi_bound_orig;
        have h_j_lt_L_minus_1 : j < L_orig - 1 := hj_bound_orig;
        have h_i_lt_L_orig : i < L_orig := Nat.lt_of_lt_pred h_i_lt_L_minus_1;
        have h_j_lt_L_orig : j < L_orig := Nat.lt_of_lt_pred h_j_lt_L_minus_1;

        simp only [List.get?_eq_get h_i_lt_L_orig, List.get?_eq_get h_j_lt_L_orig];
        -- Goal is now: c_orig_verts[i] ≠ c_orig_verts[j]

        let L_rev := c_rev_verts.length;
        have h_L_rev_eq_L_orig : L_rev = L_orig := by { simp [L_orig, c_orig_verts, List.length_reverse] };
        rw [←h_L_rev_eq_L_orig] at h_L_orig_gt_one h_i_lt_L_minus_1 h_j_lt_L_minus_1 h_i_lt_L_orig h_j_lt_L_orig;

        let k_i := L_rev - 1 - i; -- Corresponds to c_orig_verts[i]
        let k_j := L_rev - 1 - j; -- Corresponds to c_orig_verts[j]

        have h_k_i_ne_k_j : k_i ≠ k_j := by {
          intro h_eq_k; apply h_i_ne_j;
          let X := L_rev - 1;
          have h_eq_X_sub : X - i = X - j := h_eq_k;
          have h_i_le_X : i ≤ X := Nat.le_of_lt h_i_lt_L_minus_1;
          have h_j_le_X : j ≤ X := Nat.le_of_lt h_j_lt_L_minus_1;
          apply Nat.add_left_cancel; -- prove i = j from X-i = X-j
          rw [Nat.sub_add_cancel h_i_le_X];     -- LHS becomes X. Goal is X = (X-i) + j
          rw [h_eq_X_sub];                     -- Goal is X = (X-j) + j
          rw [Nat.sub_add_cancel h_j_le_X];    -- Goal is X = X
        };

        have h_cycle_rev_endpoints_eq : c_rev_verts[0] = c_rev_verts[L_rev - 1] := by {
          obtain ⟨hc_len_rev, hc_match_rev_get?⟩ := c_rev_inst.cycle_condition;
          have h_L_rev_pos_get : L_rev > 0 := by linarith [hc_len_rev];
          have h_idx0_lt_L_rev_get : 0 < L_rev := h_L_rev_pos_get;
          have h_idxL_1_lt_L_rev_get : L_rev - 1 < L_rev := Nat.sub_lt h_L_rev_pos_get Nat.one_pos;
          simp only [List.get?_eq_get h_idx0_lt_L_rev_get, List.get?_eq_get h_idxL_1_lt_L_rev_get] at hc_match_rev_get?;
          exact hc_match_rev_get?;
        };

        suffices h_target_rev: c_rev_verts[k_i] ≠ c_rev_verts[k_j] by {
           simp [c_orig_verts, List.getElem_reverse, h_i_lt_L_orig, h_j_lt_L_orig, h_L_rev_eq_L_orig];
           exact h_target_rev;
        };

        by_cases hi_zero : i = 0;
        · -- Then k_i = L_rev - 1.
          have hj_pos : j > 0 := Nat.pos_of_ne_zero (by { intro hj_eq_zero; apply h_i_ne_j; rw [hj_eq_zero, hi_zero]; });
          have hk_j_lt_L_rev_minus_1 : k_j < L_rev - 1 := by {
            dsimp [k_j]; -- Goal: L_rev - 1 - j < L_rev - 1
            let X := L_rev - 1;
            have hXpos : 0 < X := Nat.sub_pos_of_lt h_L_orig_gt_one;
            apply Nat.sub_lt_of_pos_le hj_pos (Nat.le_of_lt h_j_lt_L_minus_1);
          };
          have hk_j_ne_zero : k_j ≠ 0 := by {
            dsimp[k_j]; intro h_kj_is_0; -- h_kj_is_0 is L_rev - 1 - j = 0
            have h_Lrev_minus_1_le_j : L_rev - 1 ≤ j := Nat.sub_eq_zero_iff_le.mp h_kj_is_0;
            exact Nat.not_lt_of_le h_Lrev_minus_1_le_j h_j_lt_L_minus_1;
          };
          simp only [k_i, k_j, hi_zero, Nat.sub_zero] at *;
          rw [←h_cycle_rev_endpoints_eq]; -- Modifies goal further
          have bound_0_lt_L_rev_sub_1 : 0 < L_rev - 1 := Nat.sub_pos_of_lt h_L_orig_gt_one;
          convert c_rev_inst.distinct_internal_vertices 0 k_j bound_0_lt_L_rev_sub_1 hk_j_lt_L_rev_minus_1 (Ne.symm hk_j_ne_zero);
          { have h_idx0_lt_len : 0 < (c_rev_inst.vertices).length := Nat.lt_of_lt_pred h_i_lt_L_minus_1;
            have h_idxkj_lt_len : k_j < (c_rev_inst.vertices).length := Nat.lt_of_lt_pred hk_j_lt_L_rev_minus_1;
            simp only [List.get?_eq_get, List.get_eq_getElem, L_rev, c_rev_verts, h_idx0_lt_len, h_idxkj_lt_len, k_j]; }
        · -- i > 0, so k_i < L_rev - 1
          have hk_i_lt_L_rev_minus_1 : k_i < L_rev - 1 := by {
            dsimp [k_i]; -- Goal: L_rev - 1 - i < L_rev - 1
            let X := L_rev - 1;
            have hXpos : 0 < X := Nat.sub_pos_of_lt h_L_orig_gt_one;
            have hi_pos : 0 < i := Nat.pos_of_ne_zero hi_zero;
            apply Nat.sub_lt_of_pos_le hi_pos (Nat.le_of_lt h_i_lt_L_minus_1);
          };
          by_cases hj_zero : j = 0;
          · -- Then k_j = L_rev - 1.
            have hk_i_ne_zero : k_i ≠ 0 := by {
              dsimp[k_i]; intro h_ki_is_0; -- h_ki_is_0 is L_rev - 1 - i = 0
              have h_Lrev_minus_1_le_i : L_rev - 1 ≤ i := Nat.sub_eq_zero_iff_le.mp h_ki_is_0;
              exact Nat.not_lt_of_le h_Lrev_minus_1_le_i h_i_lt_L_minus_1;
            };
            simp only [k_i, k_j, hj_zero, Nat.sub_zero] at *;
            rw [←h_cycle_rev_endpoints_eq]; -- Modifies goal
            have bound_0_lt_L_rev_sub_1 : 0 < L_rev - 1 := Nat.sub_pos_of_lt h_L_orig_gt_one;
            convert c_rev_inst.distinct_internal_vertices k_i 0 hk_i_lt_L_rev_minus_1 bound_0_lt_L_rev_sub_1 hk_i_ne_zero;
            { have h_idxki_lt_len : k_i < (c_rev_inst.vertices).length := Nat.lt_of_lt_pred hk_i_lt_L_rev_minus_1;
              have h_idx0_lt_len : 0 < (c_rev_inst.vertices).length := (Nat.zero_lt_one.trans h_L_orig_gt_one);
              simp only [List.get?_eq_get, List.get_eq_getElem, L_rev, c_rev_verts, h_idxki_lt_len, h_idx0_lt_len, k_i, k_j]; }
          · -- Both i > 0 and j > 0.
            have hk_j_lt_L_rev_minus_1 : k_j < L_rev - 1 := by {
              dsimp [k_j]; -- Goal: L_rev - 1 - j < L_rev - 1
              let X := L_rev - 1;
              have hXpos : 0 < X := Nat.sub_pos_of_lt h_L_orig_gt_one;
              have hj_pos_local : 0 < j := Nat.pos_of_ne_zero hj_zero;
              apply Nat.sub_lt_of_pos_le hj_pos_local (Nat.le_of_lt h_j_lt_L_minus_1);
            };
            have hk_i_lt_L_rev : k_i < L_rev := Nat.lt_of_lt_pred hk_i_lt_L_rev_minus_1;
            have hk_j_lt_L_rev : k_j < L_rev := Nat.lt_of_lt_pred hk_j_lt_L_rev_minus_1;
            have h_distinct_prop := c_rev_inst.distinct_internal_vertices k_i k_j hk_i_lt_L_rev_minus_1 hk_j_lt_L_rev_minus_1 h_k_i_ne_k_j;
            simp only [List.get?_eq_get hk_i_lt_L_rev, List.get?_eq_get hk_j_lt_L_rev] at h_distinct_prop;
            exact h_distinct_prop;
      }
    };
