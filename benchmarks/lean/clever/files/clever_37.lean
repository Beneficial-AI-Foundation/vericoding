-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (l: List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
:= by
  sorry
-- </vc-theorems>