-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (s: String) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: String → List String)
-- inputs
(s: String) :=
-- spec
let spec (result: List String) :=
  let chars := s.toList;
  let first := s.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ');
  (result = [] ↔ (∀ x ∈ chars, x = ' ' ∨ x = ',') ∨ s = "") ∧
  (result ≠ [] ↔ result = [first] ++ (implementation (s.drop (first.length + 1))))

-- program termination
∃ result, implementation s = result ∧
spec result

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  sorry
-- </vc-theorems>

-- #test implementation "Hi, my name is John" = ["Hi", "my", "name", "is", "John"]
-- #test implementation "One, two, three, four, five, six" = ["One", "two", "three", "four", "five", "six"]
-- #test implementation "Hi, my name" = ["Hi", "my", "name"]
-- #test implementation "One,, two, three, four, five, six," = ["One", "two", "three", "four", "five", "six"]
-- #test implementation "" = []
-- #test implementation "ahmed     , gamal" = ["ahmed", "gamal"]