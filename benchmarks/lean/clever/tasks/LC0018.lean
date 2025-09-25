-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (string: String) (substring: String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: String → String → Nat)
-- inputs
(string substring: String) :=
-- spec
let spec (result: Nat) :=
(string.length < substring.length → result = 0)
∧
(string.length = substring.length →
((string = substring ↔ result = 1) ∧
(substring ≠ string ↔ result = 0)))
∧
(substring.length < string.length  →
let subtring_start_idx := {i: Nat | i ≤ string.length - substring.length};
let substring_occurrences := {i ∈ subtring_start_idx | (string.take (i + substring.length)).drop i = substring };
result = substring_occurrences.toFinset.card);
-- program termination
∃ result, implementation string substring = result ∧
spec result

theorem correctness
(string: String)
(substring: String)
: problem_spec implementation string substring
:= by
  sorry
-- </vc-theorems>