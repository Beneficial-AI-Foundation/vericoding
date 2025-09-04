/- 
function_signature: "def eat(number: Nat, need: Nat, remaining: Nat) -> List Nat"
docstring: |
    You're a hungry rabbit, and you already have eaten a certain number of carrots,
    but now you need to eat more carrots to complete the day's meals.
    you should return an array of [ total number of eaten carrots after your meals,
                                    the number of carrots left after your meals ]
    if there are not enough remaining carrots, you will eat all remaining carrots, but will still be hungry.

    Variables:
      @number : integer
          the number of carrots that you have eaten.
      @need : integer
          the number of carrots that you need to eat.
      @remaining : integer
          the number of remaining carrots thet exist in stock

    Constrain:
    * 0 <= number <= 1000
    * 0 <= need <= 1000
    * 0 <= remaining <= 1000
test_cases:
  - input: [5, 6, 10]
    expected_output: [11, 4]
  - input: [4, 8, 9]
    expected_output: [12, 1]
  - input: [1, 10, 10]
    expected_output: [11, 0]
  - input: [2, 11, 5]
    expected_output: [7, 0]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (a b c: Nat) : List Nat :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(impl: Nat → Nat → Nat → List Nat)
-- inputs
(number need remaining: Nat) :=
-- spec
let spec (result: List Nat) :=
number ≤ 1000 → need ≤ 1000 → remaining ≤ 1000 →
result.length = 2 ∧
(need ≤ remaining → result[0]! - need = number ∧
need = remaining - result[1]!) ∧
(remaining < need → result[0]! - remaining = number ∧
result[1]! = 0);
-- program terminates
∃ result, impl number need remaining = result ∧
-- return value satisfies spec
spec result

theorem correctness
(a b c: Nat)
: problem_spec implementation a b c :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation 5 6 10 = [11, 4]
-- #test implementation 4 8 9 = [12, 1]
-- #test implementation 1 10 10 = [11, 0]
-- #test implementation 2 11 5 = [7, 0]