-- <vc-helpers>
-- </vc-helpers>

def arrange_tiles (n : Int) : String := sorry

theorem invalid_inputs {n : Int}
  (h : n ≤ 0) : arrange_tiles n = "-1" := sorry

theorem valid_inputs_first_element {n : Int}
  (h : n > 0) : 
  let numbers := (arrange_tiles n).split (· = ' ')
  numbers.get? 0 = some (toString n) := sorry

theorem valid_inputs_length {n : Int}
  (h : n > 0) :
  let numbers := (arrange_tiles n).split (· = ' ')
  numbers.length = n := sorry

theorem valid_inputs_alternating {n : Int} (h : n > 1)
  (i : Nat) (h2 : i < n - 1) :
  let numbers := (arrange_tiles n).split (· = ' ') |>.map String.toInt!
  numbers[i+1]? = some (n + (i+2)/2) ∧ 
  numbers[i+2]? = some (n - (i+2)/2) := sorry

theorem unique_elements {n : Int}
  (h : n > 0) :
  let numbers := (arrange_tiles n).split (· = ' ') |>.map String.toInt!
  numbers.eraseDups = numbers := sorry

/-
info: '1'
-/
-- #guard_msgs in
-- #eval arrange_tiles 1

/-
info: '2 3'
-/
-- #guard_msgs in
-- #eval arrange_tiles 2

/-
info: '3 4 2'
-/
-- #guard_msgs in
-- #eval arrange_tiles 3

-- Apps difficulty: interview
-- Assurance level: unguarded