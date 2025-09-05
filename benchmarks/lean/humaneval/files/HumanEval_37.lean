/- 
function_signature: "def sort_even(l: list)"
docstring: |
    This function takes a list l and returns a list l' such that
    l' is identical to l in the odd indicies, while its values at the even indicies are equal
    to the values of the even indicies of l, but sorted.
test_cases:
  - input: [1, 2, 3]
    output: [1, 2, 3]
  - input: [5, 6, 3, 4]
    output: [3, 6, 5, 4]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (l: List Int) : List Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(l: List Int) :=
-- spec
let spec (result: List Int) :=
  l.length = result.length ∧
  let even_idx := (List.range l.length).filter (λ i => i % 2 = 0);
  let even_val_in_result := even_idx.map (λ i => result[i]!);
  let even_val := even_idx.map (λ i => l[i]!);
  (∀ i, i < l.length → (i % 2 ≠ 0 → l[i]! = result[i]!)) ∧
  List.Sorted Int.le even_val_in_result ∧
  even_val.all (λ x => even_val_in_result.count x = even_val.count x);
-- program termination
∃ result, implementation l = result ∧
spec result

theorem correctness
(l: List Int)
: problem_spec implementation l
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation [1, 2, 3] = [1, 2, 3]
-- #test implementation [5, 6, 3, 4] = [3, 6, 5, 4]