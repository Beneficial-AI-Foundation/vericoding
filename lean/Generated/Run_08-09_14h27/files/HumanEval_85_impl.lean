/- 
function_signature: "def solve(n: list[int]) -> int"
docstring: |
    Given a non-empty list of integers lst, add the even elements that are at odd indices.
test_cases:
  - input: [4, 2, 6, 7]
    output: 2
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def sumEvenAtOddIndices (lst: List Int) (startIdx: Nat) : Int :=
  match lst with
  | [] => 0
  | head :: tail =>
    let contribution := if startIdx % 2 = 1 ∧ Even head then head else 0
    contribution + sumEvenAtOddIndices tail (startIdx + 1)

def implementation (lst: List Int) : Int :=
  sumEvenAtOddIndices lst 0

def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(lst: List Int) :=
-- spec
let spec (result : Int) :=
  lst.length = 0 → result = 0 ∧
  lst.length > 0 →
    if lst.length > 1 then
      result = (if (lst[1]?.getD 0) % 2 = 0 then lst[1]?.getD 0 else 0) + implementation (lst.drop 2)
    else
      result = 0
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

-- LLM HELPER
lemma sumEvenAtOddIndices_nil (startIdx : Nat) : sumEvenAtOddIndices [] startIdx = 0 := by
  rfl

-- LLM HELPER
lemma sumEvenAtOddIndices_cons (head : Int) (tail : List Int) (startIdx : Nat) :
  sumEvenAtOddIndices (head :: tail) startIdx =
  (if startIdx % 2 = 1 ∧ Even head then head else 0) + sumEvenAtOddIndices tail (startIdx + 1) := by
  rfl

-- LLM HELPER
lemma implementation_nil : implementation [] = 0 := by
  simp [implementation, sumEvenAtOddIndices]

-- LLM HELPER
lemma implementation_single (x : Int) : implementation [x] = 0 := by
  simp [implementation, sumEvenAtOddIndices]

-- LLM HELPER
lemma implementation_cons_cons (x y : Int) (tail : List Int) :
  implementation (x :: y :: tail) = (if Even y then y else 0) + implementation tail := by
  simp [implementation]
  rw [sumEvenAtOddIndices_cons, sumEvenAtOddIndices_cons]
  simp
  rw [sumEvenAtOddIndices]
  simp
  ring

-- LLM HELPER
lemma even_iff_mod_two_eq_zero (n : Int) : Even n ↔ n % 2 = 0 := by
  simp [Even]

theorem correctness
(lst: List Int)
: problem_spec implementation lst
:= by
  simp [problem_spec]
  use implementation lst
  constructor
  · rfl
  · intro spec
    constructor
    · intro h_empty
      rw [h_empty, implementation_nil]
    · intro h_nonempty
      cases' lst with head tail
      · simp at h_nonempty
      · cases' tail with head2 tail2
        · simp [List.length]
          simp [implementation_single]
        · simp [List.length] at *
          rw [implementation_cons_cons]
          simp [List.getElem?_cons_succ]
          rw [even_iff_mod_two_eq_zero]