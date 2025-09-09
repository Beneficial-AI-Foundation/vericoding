import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (numbers: List Int) (threshold: Int) : Bool :=
  sorry

def problem_spec
-- function signature
(impl: List Int → Int → Bool)
-- inputs
(numbers: List Int)
(threshold: Int) :=
-- spec
let numbers_below_threshold :=
  ∀ i, i < numbers.length → numbers[i]! < threshold;
let spec (res: Bool) :=
(numbers.length = 0 → res) ∧
(res ↔ numbers_below_threshold)
-- program terminates
∃ result, impl numbers threshold = result ∧
-- return value satisfies spec
spec result
-- if result then spec else ¬spec

theorem correctness
(numbers: List Int)
(threshold: Int)
: problem_spec implementation numbers threshold  := by
  sorry

-- #test implementation ([1, 2, 4, 10]: List Int) 100 = true
-- #test implementation ([1, 20, 4, 10]: List Int) 5 = false