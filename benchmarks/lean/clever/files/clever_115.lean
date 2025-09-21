-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (grid: List (List Nat)) (capacity: Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: List (List Nat) → Nat → Nat)
-- inputs
(grid: List (List Nat))
(capacity: Nat) :=
-- spec
let spec (result : Nat) :=
  (grid.all (fun row => row.all (fun cell => cell = 0 ∨ cell = 1))) →
  (∃ len : Nat, grid.all (fun row => row.length = len)) →
  (result = 0 ↔ grid.length = 0) ∧
  (grid.length > 0 →
    let well_water_count := grid.head!.sum;
    result - (well_water_count / capacity) - (if well_water_count % capacity > 0 then 1 else 0) = implementation grid.tail! capacity)
-- program termination
∃ result,
  implementation grid capacity = result ∧
  spec result

theorem correctness
(grid: List (List Nat))
(capacity: Nat)
: problem_spec implementation grid capacity
:= by
  sorry
-- </vc-theorems>