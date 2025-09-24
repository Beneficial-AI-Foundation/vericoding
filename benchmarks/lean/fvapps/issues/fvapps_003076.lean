-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def even_or_odd (n : Int) : EvenOdd := sorry

theorem even_or_odd_valid (x : Int) : 
  even_or_odd x = (if x % 2 = 0 then EvenOdd.Even else EvenOdd.Odd) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem even_or_odd_consistent_add2 (x : Int) :
  even_or_odd x = even_or_odd (x + 2) := sorry 

theorem even_or_odd_alternates (x : Int) :
  even_or_odd x ≠ even_or_odd (x + 1) := sorry

theorem even_or_odd_negation (x : Int) :
  even_or_odd x = even_or_odd (-x) := sorry

/-
info: 'Even'
-/
-- #guard_msgs in
-- #eval even_or_odd 2

/-
info: 'Odd'
-/
-- #guard_msgs in
-- #eval even_or_odd 1

/-
info: 'Even'
-/
-- #guard_msgs in
-- #eval even_or_odd 0

/-
info: 'Even'
-/
-- #guard_msgs in
-- #eval even_or_odd 1545452

/-
info: 'Odd'
-/
-- #guard_msgs in
-- #eval even_or_odd 74156741

/-
info: 'Odd'
-/
-- #guard_msgs in
-- #eval even_or_odd -123

/-
info: 'Even'
-/
-- #guard_msgs in
-- #eval even_or_odd -456
-- </vc-theorems>