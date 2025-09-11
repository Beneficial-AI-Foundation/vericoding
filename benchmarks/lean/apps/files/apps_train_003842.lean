-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def monkey_count (n : Nat) : List Nat := sorry

theorem monkey_count_length {n : Nat} (h : n > 0) : 
  (monkey_count n).length = n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem monkey_count_first {n : Nat} (h : n > 0) :
  (monkey_count n).head! = 1 := sorry 

theorem monkey_count_last {n : Nat} (h : n > 0) :
  (monkey_count n).getLast! = n := sorry

/-
info: [1, 2, 3, 4, 5]
-/
-- #guard_msgs in
-- #eval monkey_count 5

/-
info: [1]
-/
-- #guard_msgs in
-- #eval monkey_count 1

/-
info: [1, 2, 3]
-/
-- #guard_msgs in
-- #eval monkey_count 3
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible