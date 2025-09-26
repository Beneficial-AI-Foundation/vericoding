-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma map_addOne_get! {l : List Int} {i : Nat} (hi : i < l.length) :
  (l.map (fun x => x + 1))[i]! = l[i]! + 1 := by
  revert i
  induction l with
  | nil =>
      intro i hi; cases hi
  | cons a l ih =>
      intro i hi
      cases i with
      | zero =>
          simp [List.map, List.get!]
      | succ i =>
          have hi' : i < l.length := by
            have : Nat.succ i < Nat.succ l.length := by
              simpa [List.length] using hi
            exact Nat.lt_of_succ_lt_succ this
          simpa [List.map, List.get!] using ih hi'

-- </vc-helpers>

-- <vc-definitions>
def implementation (numbers: List Int) : List Int :=
  numbers.map (fun x => x + 1)
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: List Int) :=
  (result.length = numbers.length) ∧
  ∀ i, i < numbers.length →
  result[i]! = numbers[i]! + 1
-- -- program termination
∃ result, implementation numbers = result ∧
spec result

theorem correctness
(numbers : List Int)
: problem_spec implementation numbers
:= by
  classical
unfold problem_spec
refine ⟨implementation numbers, rfl, ?_⟩
dsimp
constructor
· simp [implementation]
· intro i hi
  simpa [implementation] using map_addOne_get! (l := numbers) (i := i) hi
-- </vc-theorems>

-- #test implementation [1, 2, 3] = [2, 3, 4]
-- #test implementation [5, 3, 5, 2, 3, 3, 9, 0, 123] = [6, 4, 6, 3, 4, 4, 10, 1, 124]