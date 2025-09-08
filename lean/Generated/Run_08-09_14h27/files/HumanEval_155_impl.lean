/- 
function_signature: "def even_odd_count(num: int) -> Tuple[int, int]"
docstring: |
    Given an integer. return a tuple that has the number of even and odd digits respectively.
test_cases:
  - input: -12
    expected_output: [1, 1]
  - input: 123
    expected_output: [1, 2]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def count_even_odd_digits (n : Nat) : Int × Int :=
  if n = 0 then (1, 0)  -- 0 is even
  else
    let rec aux (m : Nat) (even_count odd_count : Int) : Int × Int :=
      if m = 0 then (even_count, odd_count)
      else
        let digit := m % 10
        let rest := m / 10
        if digit % 2 = 0 then
          aux rest (even_count + 1) odd_count
        else
          aux rest even_count (odd_count + 1)
    aux n 0 0

def implementation (num: Int) : Int × Int :=
  count_even_odd_digits (Int.natAbs num)

def problem_spec
-- function signature
(impl: Int → Int × Int)
-- inputs
(num: Int) :=
-- spec
let spec (result: Int × Int) :=
  let (even_count, odd_count) := result;
  let numAbs := |num|.toNat;
  let numBy10 := numAbs/10;
  let (even_count', odd_count') := impl numBy10;
  (result = impl numAbs) ∧
  (0 ≤ num → (Even num ↔ 1 + even_count' = even_count) ∧ (Odd num ↔ even_count' = even_count)) ∧
  (0 ≤ num → (Odd num ↔ 1 + odd_count' = odd_count) ∧ (Even num ↔ odd_count' = odd_count));
-- program terminates
∃ result, impl num = result ∧
-- return value satisfies spec
spec result

theorem correctness
(num: Int)
: problem_spec implementation num := by
  unfold problem_spec
  use implementation num
  constructor
  · rfl
  · unfold implementation count_even_odd_digits
    simp only [Int.natAbs_of_nonneg, Int.natAbs_neg]
    sorry

-- #test implementation -12 = (1, 1)
-- #test implementation 123 = (1, 2)