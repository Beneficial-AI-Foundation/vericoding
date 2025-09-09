import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (x : Nat) : Nat :=
  sorry

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
  sorry

-- #test implementation 0 = 0
-- #test implementation 5 = 25