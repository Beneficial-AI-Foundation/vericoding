import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (x base: Nat) : String :=
  sorry

def problem_spec
-- function signature
(implementation: Nat → Nat -> String)
-- inputs
(x base: Nat) :=
-- spec
let spec (result: String) :=
let result_array := result.toList.map (fun c => c.toNat - '0'.toNat);
let pow_array := (List.range result_array.length).map (fun i => base^(result_array.length - i - 1) * result_array[i]!);
let pow_sum := pow_array.sum;
(0 < base ∧ base ≤ 10) ∧
(∀ i, i < result_array.length →
result_array[i]! < base ∧ 0 ≤ result_array[i]! →
pow_sum = x);
-- program termination
∃ result, implementation x base = result ∧
spec result

theorem correctness
(x base : Nat)
: problem_spec implementation x base
:= by
  sorry

-- #test implementation 8 3 = '22'
-- #test implementation 8 2 = '1000'
-- #test implementation 7 2 = '111'