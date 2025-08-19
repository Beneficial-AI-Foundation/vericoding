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
def evenRange (start stop : Nat) : List Nat :=
if start > stop then []
else if start % 2 = 0 then start :: evenRange (start + 2) stop
else evenRange (start + 1) stop

def implementation (a b: Nat) : List Nat := 
let min_a_b := min a b
let max_a_b := max a b
if min_a_b = max_a_b ∧ (min_a_b % 2 = 1) then []
else 
  let start := if 2 ∣ min_a_b then min_a_b else (min_a_b + 1)
  let stop := if 2 ∣ max_a_b then max_a_b else max_a_b - 1
  evenRange start stop

-- LLM HELPER
lemma evenRange_all_even (start stop : Nat) : 
  (evenRange start stop).all (fun n => n % 2 = 0) = true := by
  sorry

-- LLM HELPER
lemma evenRange_ascending (start stop : Nat) :
  ∀ i, i < (evenRange start stop).length - 1 → 
  (evenRange start stop)[i+1]! - (evenRange start stop)[i]! = 2 := by
  sorry

-- LLM HELPER
lemma evenRange_length (start stop : Nat) (h : start ≤ stop) (h_even : start % 2 = 0) :
  1 < (evenRange start stop).length ∨ (evenRange start stop).length ≤ 1 := by
  sorry

-- LLM HELPER
lemma evenRange_bounds (start stop : Nat) (h : start ≤ stop) (h_even : start % 2 = 0) :
  (evenRange start stop).length > 0 → 
  (evenRange start stop)[0]! = start ∧ 
  (evenRange start stop)[(evenRange start stop).length - 1]! ≤ stop := by
  sorry

theorem correctness
(a b: Nat)
: problem_spec implementation a b := by
  sorry