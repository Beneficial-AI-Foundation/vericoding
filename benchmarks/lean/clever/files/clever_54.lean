-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (s0 s1: String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(impl: String → String → Bool)
-- inputs
(s0 s1: String) :=
-- spec
let spec (res: Bool) :=
  res ↔ (∀ c : Char, c ∈ s0.toList ↔ c ∈ s1.toList)
-- program terminates
∃ result, impl s0 s1 = result ∧
-- return value satisfies spec
spec result
-- if result then spec else ¬spec

theorem correctness
(s0 s1: String)
: problem_spec implementation s0 s1  := by
  sorry
-- </vc-theorems>