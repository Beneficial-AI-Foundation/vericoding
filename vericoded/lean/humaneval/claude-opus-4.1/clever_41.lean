-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def implementation (x : Nat) : Nat :=
  x * x
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(x : Nat) :=
-- spec
let spec (result: Nat) :=
  ∃ x_list : List Nat, x_list.length = x ∧ x_list.all (fun i => i = x)
  ∧ x_list.sum = result
-- -- program termination
∃ result, implementation x = result ∧
spec result

theorem correctness
(x : Nat)
: problem_spec implementation x
:= by
  unfold problem_spec
  use x * x
  constructor
  · simp [implementation]
  · use List.replicate x x
    constructor
    · simp [List.length_replicate]
    · constructor
      · simp [List.mem_replicate]
      · simp [List.sum_replicate]
-- </vc-theorems>

-- #test implementation 0 = 0
-- #test implementation 5 = 25