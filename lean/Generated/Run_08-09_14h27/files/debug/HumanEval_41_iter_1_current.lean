import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (x : Nat) : Nat :=
  x * x

-- LLM HELPER
lemma list_replicate_properties (n : Nat) :
  let x_list := List.replicate n n
  x_list.length = n ∧ x_list.all (fun i => i = n) ∧ x_list.sum = n * n := by
  simp [List.length_replicate, List.all_replicate, List.sum_replicate]

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
  · rfl
  · use List.replicate x x
    exact list_replicate_properties x