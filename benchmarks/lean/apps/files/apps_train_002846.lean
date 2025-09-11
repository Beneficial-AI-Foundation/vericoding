-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def abs (n : Int) : Int := if n ≥ 0 then n else -n

def find_digit (num : Int) (nth : Int) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem negative_nth_returns_negative_one
  (num nth : Int) (h : nth ≤ 0) :
  find_digit num nth = -1 := sorry 

theorem returns_valid_digit 
  (num nth : Int) (h : nth ≥ 1) :
  -1 ≤ find_digit num nth ∧ find_digit num nth ≤ 9 := sorry

theorem result_matches_string_length
  (num nth : Int) (h : nth ≥ 1) :
  find_digit num nth = 0 ∨ 
  (0 ≤ find_digit num nth ∧ find_digit num nth ≤ 9) := sorry

theorem single_digit_numbers
  (num nth : Int) (h1 : 0 ≤ num) (h2 : num ≤ 9) (h3 : nth ≥ 1) :
  if nth = 1
  then find_digit num nth = num 
  else find_digit num nth = 0 := sorry

theorem zero_number :
  find_digit 0 1 = 0 ∧ find_digit 0 5 = 0 := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_digit 5673 4

/-
info: 8
-/
-- #guard_msgs in
-- #eval find_digit -2825 3

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_digit 0 20

/-
info: -1
-/
-- #guard_msgs in
-- #eval find_digit 65 0

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_digit -456 5
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded