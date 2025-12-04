import ChipFiringWithLean.Basic
import ChipFiringWithLean.Config
import ChipFiringWithLean.Orientation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Tactic

set_option linter.unusedVariables false

-- Assume V is a finite type with decidable equality
variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]

namespace CF

open Finset BigOperators List

/-- Perform a borrowing move at vertex `v`. Inverse of `firing_move`.
`v` gains `deg(v)` chips, neighbors `w` lose `num_edges G v w` chips. -/
@[simp]
noncomputable def borrowing_move (G : CFGraph V) (D : CFDiv V) (v : V) : CFDiv V :=
  fun w =>
    if _ : w = v then -- Use underscore for unused hypothesis
      D v + vertex_degree G v -- Use vertex_degree function
    else
      D w - num_edges G v w

/-- Check if a divisor is effective (all vertices non-negative). From Basic.lean -/
@[simp]
def is_effective (D : CFDiv V) : Bool := decide (∀ v, D v ≥ 0)

/--
Greedy Algorithm for the dollar game (Algorithm 1).
Repeatedly chooses an in-debt vertex `v` that hasn't borrowed yet (`v ∉ M`)
and performs a borrowing move at `v`, adding `v` to `M`.
Returns `(winnable, script)` where `winnable` is true if an effective divisor is reached,
and `script` is the net borrowing count for each vertex if winnable.
-/
@[simp]
noncomputable def greedyWinnable (G : CFGraph V) (D : CFDiv V) : Bool × Option (CFDiv V) := -- Changed to CFDiv V
  let rec loop (current_D : CFDiv V) (M : Finset V) (script : CFDiv V) (fuel : Nat) : Bool × Option (CFDiv V) := -- Changed to CFDiv V
    if h_fuel_zero : fuel = 0 then (false, none) -- Fuel exhaustion implies failure
    else if is_effective current_D then (true, some script)
    else if M = Finset.univ then (false, none) -- All vertices borrowed, still not effective
    else
      -- Find a vertex v such that D(v) < 0 and v ∉ M
      match (Finset.univ \ M).toList.find? (fun v => current_D v < 0) with -- Use Finset set difference \
      | some v =>
          let next_D := borrowing_move G current_D v
          let next_M := insert v M -- Correct insert syntax
          -- Update script: decrement count for borrowing vertex v
          let next_script : CFDiv V := script - one_chip v -- Type is now CFDiv V
          loop next_D next_M next_script (fuel - 1)
      | none => -- No vertex in V \ M is in debt, but D is not effective.
          -- This state implies unwinnability because we can't make progress.
          (false, none)
  termination_by fuel
  decreasing_by simp_wf; exact Nat.pos_of_ne_zero h_fuel_zero -- Simpler explicit proof
  -- Initial call with generous fuel
  let max_fuel := Fintype.card V * Fintype.card V
  loop D ∅ (0 : CFDiv V) max_fuel -- Initialize script as (0 : CFDiv V)

/--
Calculates the out-degree of a vertex `v` with respect to a set `S`.
This counts the number of edges from `v` to vertices *outside* `S` (including `q`).
`outdeg G S v = |{ w | ∃ edge (v, w) in G.edges and w ∉ S }|`
-/
def dhar_outdeg (G : CFGraph V) (S : Finset V) (v : V) : ℤ :=
  ∑ w in Finset.univ.filter (λ w => w ∉ S), (num_edges G v w : ℤ)

/--
Helper function for Dhar's burning loop. Finds a vertex `v` in `S` such that `c(v) < dhar_outdeg G S v`.
Returns `some v` if found, `none` otherwise.
Requires `q` to ensure we operate on configurations correctly, although `q` itself isn't directly used in the condition check.
-/
noncomputable def findBurnableVertex (G : CFGraph V) (c : V → ℤ) (S : Finset V) : Option { v : V // v ∈ S } :=
  -- Iterate through the list representation and find the first match
  -- Need to get proof v ∈ S, which is guaranteed by iterating S.toList
  let p := fun v => decide (c v < dhar_outdeg G S v) -- Use decide
  match h : S.toList.find? p with -- Use find? directly now (List is open)
  | some v =>
    -- Prove v is in the original finset S
    have h_mem_list : v ∈ S.toList := List.mem_of_find?_eq_some h
    have h_mem_finset : v ∈ S := Finset.mem_toList.mp h_mem_list
    some ⟨v, h_mem_finset⟩
  | none => none

/--
The core iterative burning process of Dhar's algorithm (Algorithm 2).
Given a configuration `c` (represented as `V → ℤ` for simplicity here, assuming non-negativity outside `q` is handled externally)
and a sink `q`, it finds the set of unburnt vertices `S ⊆ V \ {q}` which forms a legal firing set.
The set `S` is empty if and only if `c` restricted to `V \ {q}` is superstable relative to `q`.

Implementation uses well-founded recursion on the size of the set S.
-/
@[simp]
noncomputable def dharBurningSet (G : CFGraph V) (q : V) (c : V → ℤ) : Finset V :=
  let initial_S := Finset.univ.erase q
  let rec loop (S : Finset V) (fuel : Nat) : Finset V :=
    -- Check fuel for termination safety
    if h_fuel_zero : fuel = 0 then S -- Name hypothesis
    else
      match findBurnableVertex G c S with
      -- If a burnable vertex v is found, remove it and recurse
      | some ⟨v, hv⟩ => loop (S.erase v) (fuel - 1)
      -- If no burnable vertex found in S, S is stable, return it
      | none        => S
  termination_by fuel
  decreasing_by simp_wf; exact Nat.pos_of_ne_zero h_fuel_zero -- Simpler explicit proof
  loop initial_S (Fintype.card V + 1)

/-- Helper function to fire a set of vertices `S` on a divisor `D`. -/
@[simp]
noncomputable def fireSet (G : CFGraph V) (D : CFDiv V) (S : Finset V) : CFDiv V :=
  -- Use foldl directly now (List is open)
  foldl (fun current_D v => firing_move G current_D v) D S.toList

/-- Calculates the degree of a divisor. -/
@[simp]
def degree (D : CFDiv V) : ℤ :=
  ∑ v in Finset.univ, D v

/--
Preprocessing Step for Algorithm 3/4: Fires `q` repeatedly until `D(v) ≥ 0` for all `v ≠ q`.
Requires sufficient total degree in the graph. Uses fuel for termination guarantee.
Returns `none` if fuel runs out, implying potential unwinnability or insufficient fuel.
-/
noncomputable def makeNonNegativeExceptQ (G : CFGraph V) (q : V) (D : CFDiv V) (max_fuel : Nat) : Option (CFDiv V) :=
  let rec loop (current_D : CFDiv V) (fuel : Nat) : Option (CFDiv V) :=
    if h_fuel_zero : fuel = 0 then none -- Name hypothesis
    else
      -- Check if any vertex v != q has D(v) < 0
      let non_q_vertices := Finset.univ.erase q
      -- Use `find?` to efficiently check for a negative vertex
      match non_q_vertices.toList.find? (fun v => current_D v < 0) with
      | none => some current_D -- Goal reached: all v != q are non-negative
      | some _ => -- Found a vertex v != q with current_D v < 0
          -- Fire q and continue
          loop (firing_move G current_D q) (fuel - 1)
  termination_by fuel
  decreasing_by simp_wf; exact Nat.pos_of_ne_zero h_fuel_zero -- Simpler explicit proof
  loop D max_fuel

/--
Finds the unique q-reduced divisor linearly equivalent to D (Algorithm 3).
Starts from divisor D, performs preprocessing (firing q until others non-negative),
then repeatedly finds the maximal legal firing set S ⊆ V \ {q}
using `dharBurningSet` and fires S until `dharBurningSet` returns an empty set.
Returns `none` if preprocessing fails (fuel exhaustion or insufficient degree).
-/
@[simp]
noncomputable def findQReducedDivisor (G : CFGraph V) (q : V) (D : CFDiv V) : Option (CFDiv V) :=
  -- Preprocessing: Fire q until D(v) >= 0 for v != q
  -- Use a large fixed Nat fuel amount.
  let preprocess_fuel : Nat := Fintype.card V * Fintype.card V * Fintype.card V -- Use Nat constant
  match makeNonNegativeExceptQ G q D preprocess_fuel with
  | none => none -- Preprocessing failed
  | some D_preprocessed =>
      let rec loop (current_D : CFDiv V) (fuel : Nat) : CFDiv V :=
        if h_fuel_zero : fuel = 0 then -- Name hypothesis
          -- Fuel exhausted in main loop, return current state (might not be fully q-reduced)
          current_D
        else
          -- Use current_D as the configuration function for dharBurningSet
          let S := dharBurningSet G q current_D
          -- If the set S is non-empty, fire it and continue looping
          if hs : S.Nonempty then
            loop (fireSet G current_D S) (fuel - 1)
          else
            -- S is empty, the divisor is q-reduced
            current_D
      termination_by fuel
      decreasing_by simp_wf; exact Nat.pos_of_ne_zero h_fuel_zero -- Simpler explicit proof
      -- Estimate fuel for main loop: Number of possible firing sets? Use a large number.
      let main_loop_fuel := Fintype.card V * Fintype.card V * Fintype.card V + 1
      some (loop D_preprocessed main_loop_fuel)

/--
Burning Algorithm (User Request): Simulates the fire spread from `q` in Dhar's algorithm
on a configuration `c` (represented as `V → ℤ`).
Returns the set of unburnt vertices `S ⊆ V \ {q}`.
This is equivalent to `dharBurningSet`.

Note: Assumes `c` represents a configuration valid w.r.t `q`, typically non-negative on `V \ {q}`.
-/
@[simp]
noncomputable def burn (G : CFGraph V) (q : V) (c : V → ℤ) : Finset V :=
  dharBurningSet G q c

/--
Dhar's Algorithm (User Request Wrapper): Finds the v-reduced divisor D' equivalent to D.
This wraps `findQReducedDivisor`. Returns Option since reduction might fail.
-/
@[simp]
noncomputable def dhar (G : CFGraph V) (D : CFDiv V) (v : V) : Option (CFDiv V) :=
  findQReducedDivisor G v D

/--
Efficient Winnability Determination Algorithm (Algorithm 4).
Checks if the divisor D is winnable by finding the q-reduced equivalent Dq
and checking if Dq(q) ≥ 0.
Requires selection of a source vertex `q`. Returns `false` if reduction process fails.
-/
@[simp]
noncomputable def isWinnable (G : CFGraph V) (q : V) (D : CFDiv V) : Bool :=
  match findQReducedDivisor G q D with
  | none => false -- Reduction process failed (preprocessing or main loop fuel)
  | some D_q => D_q q >= 0

/--
Helper to calculate incoming "burning" degree for vertex `v` from set `B`.
Sums `num_edges` from `u` in `B` to `v`.
-/
def burning_indeg (G : CFGraph V) (B : Finset V) (v : V) : ℤ :=
  ∑ u in B, (num_edges G u v : ℤ)

/--
Orientation-based Dhar's Algorithm (Algorithm 5).
Takes a nonnegative configuration `c` relative to `q`.
Returns the final stable set `S ⊆ V \ {q}` (empty iff `c` is superstable)
and a multiset `O` of directed edges `(u, v)` where fire spread from `u` to `v`.

Note: Assumes `c` is non-negative on `V \ {q}`.
The returned multiset `O` represents the edges oriented *by* the burning process.
It may not form a complete `CFOrientation` structure directly if not all edges are involved.
-/
@[simp]
noncomputable def dharBurningSetWithOrientation (G : CFGraph V) (q : V) (c : V → ℤ)
  : Finset V × Multiset (V × V) :=
  let initial_S := Finset.univ.erase q
  let initial_B := {q}
  let initial_O := (∅ : Multiset (V × V))

  let rec loop (current_S : Finset V) (current_B : Finset V) (current_O : Multiset (V × V)) (fuel : Nat)
    : Finset V × Multiset (V × V) :=
    if h_fuel : fuel = 0 then (current_S, current_O) -- Fuel exhausted, return current state
    else
      -- Find vertices in S that burn in this step
      let newly_burned_list := current_S.toList.filter (fun v => burning_indeg G current_B v > c v)
      let newly_burned := newly_burned_list.toFinset -- Use List.toFinset

      -- If no new vertices burned, the process stabilizes
      if newly_burned.card = 0 then (current_S, current_O) -- Use card = 0 check
      else
        -- Update S and B
        let next_S := current_S.filter (fun v => v ∉ newly_burned) -- Manual set difference
        let next_B := current_B ∪ newly_burned

        -- Update Orientation: Add edges from current_B to newly_burned
        -- Use Finset.sum for clarity and potentially better type inference
        let edges_to_add : Multiset (V × V) :=
          Finset.sum newly_burned (fun v_new => -- Sum over newly burned vertices
            Finset.sum current_B (fun u => -- For each u in the burning set
              Multiset.replicate (num_edges G u v_new) (u, v_new) -- Create edges u -> v_new
            )
          )

        let next_O := current_O + edges_to_add

        -- Recurse
        loop next_S next_B next_O (fuel - 1)

  termination_by fuel
  decreasing_by simp_wf; exact Nat.pos_of_ne_zero h_fuel -- Use robust termination proof

  -- Initial call with fuel based on number of vertices
  loop initial_S initial_B initial_O (Fintype.card V + 1)

end CF
