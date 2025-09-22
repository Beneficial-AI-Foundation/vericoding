-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (lst1: List String) (lst2: List String) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: List String → List String → List String)
-- inputs
(lst1: List String) (lst2: List String) :=
let sum_chars (xs: List String) : Int :=
  xs.foldl (λ acc a => acc + a.length) 0;
-- spec
let spec (result : List String) :=
  ((result = lst1) ∨ (result = lst2))
  ∧
  (sum_chars result ≤ sum_chars lst1)
  ∧
  (sum_chars result ≤ sum_chars lst2)
  ∧
  ((sum_chars lst1 = sum_chars lst2) → (result = lst1))
-- program termination
∃ result, implementation lst1 lst2 = result ∧
spec result

theorem correctness
(lst1: List String) (lst2: List String)
: problem_spec implementation lst1 lst2
:= by
  sorry
-- </vc-theorems>