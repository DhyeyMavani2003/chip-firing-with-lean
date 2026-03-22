import ChipFiringWithLean.Orientation

set_option linter.unusedVariables false

namespace CF

/-!
## Computational algorithms for chip-firing

This file implements the main computational algorithms for chip-firing on graphs:

- `greedyWinnable`: Greedy dollar game solver (Algorithm 1).
- `dharBurningSet`: Dhar's burning algorithm, returning the set of unburnt vertices (Algorithm 2).
- `findQReducedDivisor`: Finds the unique $q$-reduced divisor linearly equivalent to a given
  divisor (Algorithm 3).
- `isWinnable`: Winnability check via $q$-reduction (Algorithm 4).
- `dharBurningSetWithOrientation`: Dhar's burning algorithm with orientation tracking (Algorithm 5).
-/

open Finset BigOperators List

/-- Check if a divisor is effective (all vertices non-negative). From `Basic.lean`. -/
@[simp]
def is_effective (D : CFDiv G) : Bool := decide (∀ v, D v ≥ 0)

/--
Greedy Algorithm for the dollar game (Algorithm 1).
Repeatedly chooses an in-debt vertex `v` that hasn't borrowed yet (`v ∉ M`)
and performs a borrowing move at `v`, adding `v` to `M`.
Returns `(winnable, script)` where `winnable` is true if an effective divisor is reached,
and `script` is the net borrowing count for each vertex if winnable.
-/
@[simp]
noncomputable def greedyWinnable (G : CFGraph) (D : CFDiv G) : Bool × Option (CFDiv G) :=
  let rec loop (current_D : CFDiv G) (M : Finset G.V) (script : CFDiv G) (fuel : Nat) : Bool × Option (CFDiv G) :=
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
          let next_script : CFDiv G := script - one_chip v
          loop next_D next_M next_script (fuel - 1)
      | none => -- No vertex in `G.V \ M` is in debt, but `D` is not effective.
          -- This state implies unwinnability because we can't make progress.
          (false, none)
  termination_by fuel
  decreasing_by simp_wf; exact Nat.pos_of_ne_zero h_fuel_zero -- Simpler explicit proof
  -- Initial call with generous fuel
  let max_fuel := Fintype.card G.V * Fintype.card G.V
  loop D ∅ (0 : CFDiv G) max_fuel -- Initialize script as (0 : CFDiv G)

/--
Calculates the out-degree of a vertex `v` with respect to a set `S`.
This counts the number of edges from `v` to vertices *outside* `S` (including `q`).
`outdeg G S v = |{ w | ∃ edge (v, w) in G.edges and w ∉ S }|`
-/
def dhar_outdeg (G : CFGraph) (S : Finset G.V) (v : G.V) : ℤ :=
  ∑ w ∈ Finset.univ.filter (λ w => w ∉ S), (num_edges G v w : ℤ)

/-- Find a vertex `v` in `S` such that `c(v) < dhar_outdeg G S v` (a "burnable" vertex).
Returns `some v` if found, `none` otherwise. -/
noncomputable def findBurnableVertex (G : CFGraph) (c : G.V → ℤ) (S : Finset G.V) : Option { v : G.V // v ∈ S } :=
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
Given a configuration `c` (represented as `G.V → ℤ` for simplicity here, assuming
non-negativity outside `q` is handled externally) and a sink `q`, it finds the set of
unburnt vertices `S ⊆ G.V \ {q}` which forms a legal firing set. The set `S` is empty if
and only if `c` restricted to `G.V \ {q}` is superstable relative to `q`.

Implementation uses well-founded recursion on the size of the set S.
-/
@[simp]
noncomputable def dharBurningSet (G : CFGraph) (q : G.V) (c : G.V → ℤ) : Finset G.V :=
  let initial_S := Finset.univ.erase q
  let rec loop (S : Finset G.V) (fuel : Nat) : Finset G.V :=
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
  loop initial_S (Fintype.card G.V + 1)

/-- Helper function to fire a set of vertices `S` on a divisor `D`. -/
@[simp]
noncomputable def fireSet (G : CFGraph) (D : CFDiv G) (S : Finset G.V) : CFDiv G :=
  -- Use foldl directly now (List is open)
  foldl (fun current_D v => firing_move G current_D v) D S.toList

/-- Calculates the degree of a divisor. -/
@[simp]
def degree (D : CFDiv G) : ℤ :=
  ∑ v ∈ Finset.univ, D v

/--
Preprocessing Step for Algorithm 3/4: Fires `q` repeatedly until `D(v) ≥ 0` for all `v ≠ q`.
Requires sufficient total degree in the graph. Uses fuel for termination guarantee.
Returns `none` if fuel runs out, implying potential unwinnability or insufficient fuel.
-/
noncomputable def makeNonNegativeExceptQ (G : CFGraph) (q : G.V) (D : CFDiv G) (max_fuel : Nat) : Option (CFDiv G) :=
  let rec loop (current_D : CFDiv G) (fuel : Nat) : Option (CFDiv G) :=
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
Finds the unique q-reduced divisor linearly equivalent to `D` (Algorithm 3).
Starts from divisor D, performs preprocessing (firing q until others non-negative),
then repeatedly finds the maximal legal firing set `S ⊆ G.V \ {q}`
using `dharBurningSet` and fires S until `dharBurningSet` returns an empty set.
Returns `none` if preprocessing fails (fuel exhaustion or insufficient degree).
-/
@[simp]
noncomputable def findQReducedDivisor (G : CFGraph) (q : G.V) (D : CFDiv G) : Option (CFDiv G) :=
  -- Preprocessing: Fire q until D(v) >= 0 for v != q
  -- Use a large fixed Nat fuel amount.
  let preprocess_fuel : Nat := Fintype.card G.V * Fintype.card G.V * Fintype.card G.V -- Use Nat constant
  match makeNonNegativeExceptQ G q D preprocess_fuel with
  | none => none -- Preprocessing failed
  | some D_preprocessed =>
      let rec loop (current_D : CFDiv G) (fuel : Nat) : CFDiv G :=
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
      let main_loop_fuel := Fintype.card G.V * Fintype.card G.V * Fintype.card G.V + 1
      some (loop D_preprocessed main_loop_fuel)

/-- Simulates the fire spread from `q` in Dhar's algorithm on a configuration `c`.
Returns the set of unburnt vertices $S \subseteq G.V \setminus \{q\}$.
Equivalent to `dharBurningSet`. -/
@[simp]
noncomputable def burn (G : CFGraph) (q : G.V) (c : G.V → ℤ) : Finset G.V :=
  dharBurningSet G q c

/-- Finds the `v`-reduced divisor linearly equivalent to `D`. Wraps `findQReducedDivisor`.
Returns `none` if the reduction process fails. -/
@[simp]
noncomputable def dhar (G : CFGraph) (D : CFDiv G) (v : G.V) : Option (CFDiv G) :=
  findQReducedDivisor G v D

/--
Efficient Winnability Determination Algorithm (Algorithm 4).
Checks if the divisor D is winnable by finding the q-reduced equivalent Dq
and checking if Dq(q) ≥ 0.
Requires selection of a source vertex `q`. Returns `false` if reduction process fails.
-/
@[simp]
noncomputable def isWinnable (G : CFGraph) (q : G.V) (D : CFDiv G) : Bool :=
  match findQReducedDivisor G q D with
  | none => false -- Reduction process failed (preprocessing or main loop fuel)
  | some D_q => D_q q >= 0

/--
Helper to calculate incoming "burning" degree for vertex `v` from set `B`.
Sums `num_edges` from `u` in `B` to `v`.
-/
def burning_indeg (G : CFGraph) (B : Finset G.V) (v : G.V) : ℤ :=
  ∑ u ∈ B, (num_edges G u v : ℤ)

/--
Orientation-based Dhar's Algorithm (Algorithm 5).
Takes a nonnegative configuration `c` relative to `q`.
Returns the final stable set `S ⊆ G.V \ {q}` (empty iff `c` is superstable)
and a multiset `O` of directed edges `(u, v)` where fire spread from `u` to `v`.

Note: Assumes `c` is non-negative on `G.V \ {q}`.
The returned multiset `O` represents the edges oriented *by* the burning process.
It may not form a complete `CFOrientation` structure directly if not all edges are involved.
-/
@[simp]
noncomputable def dharBurningSetWithOrientation (G : CFGraph) (q : G.V) (c : G.V → ℤ)
  : Finset G.V × Multiset (G.V × G.V) :=
  let initial_S := Finset.univ.erase q
  let initial_B := {q}
  let initial_O := (∅ : Multiset (G.V × G.V))

  let rec loop (current_S : Finset G.V) (current_B : Finset G.V) (current_O : Multiset (G.V × G.V)) (fuel : Nat)
    : Finset G.V × Multiset (G.V × G.V) :=
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
        let edges_to_add : Multiset (G.V × G.V) :=
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
  loop initial_S initial_B initial_O (Fintype.card G.V + 1)

end CF
