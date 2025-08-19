import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: Nat → Nat → List Nat)
-- inputs
(a b : Nat) :=
let isAscendingBy2 (r : List Nat) :=
∀ i, i < r.length - 1 → r[i+1]! - r[i]! = 2
-- spec
let spec (result: List Nat) :=
result.all (fun n => n % 2 = 0) ∧ isAscendingBy2 result ∧
1 < result.length ∧
let min_a_b := min a b;
let max_a_b := max a b;
if min_a_b = max_a_b ∧ (min_a_b % 2 = 1)
then result = []
else ((result[0]! = if 2 ∣ min_a_b then min_a_b else (min_a_b + 1)) ∧
(result[result.length-1]! = if 2 ∣ max_a_b then max_a_b else max_a_b - 1))
-- program terminates
∃ result, impl a b = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def evenRange (start finish: Nat) : List Nat :=
if start > finish then []
else if start % 2 = 0 then start :: evenRange (start + 2) finish
else evenRange (start + 1) finish

def implementation (a b: Nat) : List Nat := 
let min_a_b := min a b
let max_a_b := max a b
if min_a_b = max_a_b ∧ (min_a_b % 2 = 1) then []
else 
  let start := if 2 ∣ min_a_b then min_a_b else (min_a_b + 1)
  let finish := if 2 ∣ max_a_b then max_a_b else max_a_b - 1
  evenRange start finish

-- LLM HELPER
lemma evenRange_all_even (start finish: Nat) (h: start % 2 = 0) : 
  (evenRange start finish).all (fun n => n % 2 = 0) := by
  sorry

-- LLM HELPER
lemma evenRange_ascending_by_2 (start finish: Nat) (h: start % 2 = 0) : 
  let r := evenRange start finish
  ∀ i, i < r.length - 1 → r[i+1]! - r[i]! = 2 := by
  sorry

-- LLM HELPER
lemma evenRange_length_gt_1 (start finish: Nat) (h1: start % 2 = 0) (h2: start + 2 ≤ finish) : 
  1 < (evenRange start finish).length := by
  sorry

-- LLM HELPER
lemma evenRange_first_last (start finish: Nat) (h1: start % 2 = 0) (h2: start ≤ finish) : 
  let r := evenRange start finish
  r ≠ [] → r[0]! = start ∧ r[r.length-1]! = finish := by
  sorry

theorem correctness
(a b: Nat)
: problem_spec implementation a b := by
  sorry