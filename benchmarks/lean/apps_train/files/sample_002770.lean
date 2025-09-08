/-
*** No Loops Allowed ***

You will be given an array (a) and a limit value (limit). You must check that all values in the array are below or equal to the limit value. If they are, return true. Else, return false.

You can assume all values in the array are numbers.

Do not use loops. Do not modify input array.

Looking for more, loop-restrained fun? Check out the other kata in the series:

 https://www.codewars.com/kata/no-loops-2-you-only-need-one
 https://www.codewars.com/kata/no-loops-3-copy-within
-/

def small_enough (numbers : List Int) (limit : Int) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def list_maximum (l : List Int) : Option Int :=
  l.foldl (fun acc x => match acc with
    | none => some x
    | some m => some (max m x)) none

theorem small_enough_characterization (numbers : List Int) (limit : Int) 
    (h : numbers ≠ []) : 
  small_enough numbers limit = ((list_maximum numbers).getD 0 ≤ limit) :=
  sorry

theorem small_enough_at_maximum (numbers : List Int) (h : numbers ≠ []) :
  let max_val := (list_maximum numbers).getD 0
  small_enough numbers max_val = true ∧
  small_enough numbers (max_val - 1) = false :=
  sorry

theorem small_enough_scaling (numbers : List Int) (factor : Int)
    (h : numbers ≠ []) (h_pos : factor > 0) :
  let max_val := (list_maximum numbers).getD 0
  let scaled_numbers := numbers.map (· * factor)
  small_enough scaled_numbers (max_val * factor) = small_enough numbers max_val :=
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval small_enough [66, 101] 200

/-
info: False
-/
-- #guard_msgs in
-- #eval small_enough [78, 117, 110, 99, 104, 117, 107, 115] 100

/-
info: True
-/
-- #guard_msgs in
-- #eval small_enough [101, 45, 75, 105, 99, 107] 107

-- Apps difficulty: introductory
-- Assurance level: unguarded