-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (strings: List String) (substring: String): List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: List String → String → List String)
-- inputs
(strings: List String)
(substring: String)
:=
-- spec
let spec (result: List String) :=
(∀ i, i < result.length → result[i]!.containsSubstr substring →
∀ j, j < strings.length ∧ strings[j]!.containsSubstr substring → strings[j]! ∈ result →
∀ j, j < result.length → result.count result[j]! = strings.count result[j]!);
-- program termination
∃ result, implementation strings substring = result ∧
spec result

theorem correctness
(strings: List String)
(substring: String)
: problem_spec implementation strings substring
:= by
  sorry
-- </vc-theorems>