/- 
function_signature: "def circular_shift(x: Int, shift: Int) -> String"
docstring: |
    Circular shift the digits of the integer x, shift the digits right by shift
    and return the result as a string.
    If shift > number of digits, return digits reversed.
test_cases:
  - input: [12, 1]
    expected_output: 21
  - input: [12, 2]
    expected_output: 12
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (x shift: Nat) : String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: Nat → Nat → String)
-- inputs
(x shift: Nat) :=
let isReverse (s: String) : Bool :=
  let n := s.length;
  ∀ i, i < n / 2 → s.get! ⟨i⟩ = s.get! ⟨n - 1 - i⟩;
-- spec
let spec (result: String) :=
let x_str := Nat.repr x;
result.length = x_str.length ∧
(x_str.length < shift → isReverse x_str) ∧
(shift ≤ x_str.length →
  x_str.take shift = result.drop (x_str.length - shift) ∧
  x_str.drop shift = result.take (x_str.length - shift));
-- program termination
∃ result, implementation x shift = result ∧
spec result

theorem correctness
(x shift: Nat)
: problem_spec implementation x shift
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation (12 : Int) (1 : Int) = "21"
-- #test implementation (12 : Int) (2 : Int) = "12"