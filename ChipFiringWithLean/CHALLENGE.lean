import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Matrix.Mul

/-! This self-contained module is the auditable statement layer. -/

universe u

open Multiset Finset

structure CFGraph where
  V : Type u
  [instDecidableEq : DecidableEq V]
  [instFintype : Fintype V]
  [instNonempty : Nonempty V]
  (edges : Multiset (V × V))
  (loopless : ∀ v, (v, v) ∉ edges)

attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty

def num_edges (G : CFGraph) (v w : G.V) : ℕ :=
  Multiset.card (G.edges.filter (λ e => e = (v, w) ∨ e = (w, v)))

def graph_connected (G : CFGraph) : Prop :=
  ∀ S : Finset G.V, (∃ (v w : G.V), v ∈ S ∧ w ∉ S) →
    (∃ v ∈ S, ∃ w ∉ S, num_edges G v w > 0)

def genus (G : CFGraph) : ℤ :=
  Multiset.card G.edges - Fintype.card G.V + 1

def vertex_degree (G : CFGraph) (v : G.V) : ℤ :=
  ∑ u : G.V, (num_edges G v u : ℤ)

abbrev CFDiv (G : CFGraph) := G.V → ℤ

def firing_vector (G : CFGraph) (v : G.V) : CFDiv G :=
  λ w => if w = v then -vertex_degree G v else num_edges G v w

def principal_divisors (G : CFGraph) : AddSubgroup (CFDiv G) :=
  AddSubgroup.closure (Set.range (firing_vector G))

def linear_equiv (G : CFGraph) (D D' : CFDiv G) : Prop :=
  D' - D ∈ principal_divisors G

def effective {G : CFGraph} (D : CFDiv G) : Prop :=
  ∀ v : G.V, D v ≥ 0

def Eff (G : CFGraph) : AddSubmonoid (CFDiv G) :=
  { carrier := {D : CFDiv G | effective D},
    zero_mem' := by
      simp only [effective, ge_iff_le, Set.mem_ofPred_eq, Pi.zero_apply, Std.le_refl, implies_true]
    add_mem' := by
      intro D₁ D₂ h_eff1 h_eff2 v
      exact add_nonneg (h_eff1 v) (h_eff2 v) }

def winnable (G : CFGraph) (D : CFDiv G) : Prop :=
  ∃ D' ∈ Eff G, linear_equiv G D D'

def deg {G : CFGraph} : CFDiv G →+ ℤ := {
  toFun := λ D => ∑ v, D v,
  map_zero' := by
    simp only [Pi.zero_apply, sum_const_zero],
  map_add' := by
    intro D₁ D₂
    simp only [Pi.add_apply, sum_add_distrib],
}

def eff_of_degree (G : CFGraph) (k : ℤ) : Set (CFDiv G) :=
  {E | effective E ∧ deg E = k}

def rank_geq (G : CFGraph) (D : CFDiv G) (k : ℤ) : Prop :=
  ∀ E ∈ eff_of_degree G k, winnable G (D-E)

def rank_eq (G : CFGraph) (D : CFDiv G) (r : ℤ) : Prop :=
  rank_geq G D r ∧ ¬(rank_geq G D (r+1))

def canonical_divisor (G : CFGraph) : CFDiv G :=
  λ v => (vertex_degree G v) - 2

namespace Propositions

theorem rank_well_defined (G : CFGraph) (D : CFDiv G) :
    (∃ r : ℤ, rank_eq G D r) ∧
      ∀ r₁ r₂ : ℤ, rank_eq G D r₁ → rank_eq G D r₂ → r₁ = r₂ := by
  sorry

theorem riemann_roch {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) :
    ∀ r rdual : ℤ, rank_eq G D r → rank_eq G (canonical_divisor G - D) rdual →
      r - rdual = deg D + 1 - genus G := by
  sorry

theorem clifford {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) :
    ∀ r rdual : ℤ, rank_eq G D r → rank_eq G (canonical_divisor G - D) rdual →
      0 ≤ r → 0 ≤ rdual → (r : ℚ) ≤ (deg D : ℚ) / 2 := by
  sorry

end Propositions
