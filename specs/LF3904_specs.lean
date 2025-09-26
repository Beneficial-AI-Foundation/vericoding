-- <vc-preamble>
def List.sum : List Nat → Nat 
  | [] => 0
  | (x::xs) => x + sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum_from_string (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_single_number (n : Nat) :
  sum_from_string (toString n) = n :=
  sorry

theorem sum_empty_string :
  sum_from_string "" = 0 :=
  sorry

/-
info: 2021
-/
-- #guard_msgs in
-- #eval sum_from_string "In 2015, I want to know how much does iPhone 6+ cost?"

/-
info: 4
-/
-- #guard_msgs in
-- #eval sum_from_string "1+1=2"

/-
info: 0
-/
-- #guard_msgs in
-- #eval sum_from_string "Hello World"
-- </vc-theorems>