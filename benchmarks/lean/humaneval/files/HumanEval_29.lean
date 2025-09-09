import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (strings: List String) (pref: String) : List String :=
  sorry

def problem_spec
-- function signature
(implementation: List String → String → List String)
-- inputs
(strings: List String)
(pref: String) :=
-- spec
let spec (result: List String) :=
result.all (λ s => s.startsWith pref) ∧
result.all (λ s => s ∈ strings) ∧
strings.all (λ s => s.startsWith pref → s ∈ result) ∧
∀ s : String, s ∈ result → result.count s = strings.count s;
-- program termination
∃ result, implementation strings pref = result ∧
spec result

theorem correctness
(strings: List String)
(pref: String)
: problem_spec implementation strings pref
:= by
  sorry

-- #test implementation [] "a" = []
-- #test implementation ["abc", "bcd", "cde", "array"] "a" = ["abc", "array"]