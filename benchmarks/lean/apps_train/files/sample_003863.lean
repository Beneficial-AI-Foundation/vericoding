/-
Given an array of numbers, return the difference between the largest and smallest values. 

For example:

`[23, 3, 19, 21, 16]` should return `20` (i.e., `23 - 3`).

`[1, 434, 555, 34, 112]` should return `554` (i.e., `555 - 1`).

The array will contain a minimum of two elements. Input data range guarantees that `max-min` will cause no integer overflow.
-/

def List.maximum : List Int → Option Int 
  | [] => none
  | (h::t) => some (t.foldl max h)

def List.minimum : List Int → Option Int
  | [] => none
  | (h::t) => some (t.foldl min h)

-- <vc-helpers>
-- </vc-helpers>

def between_extremes (nums : List Int) : Int :=
  sorry

theorem between_extremes_nonnegative (nums : List Int) (h : nums ≠ []) :
  between_extremes nums ≥ 0 := 
  sorry

theorem between_extremes_singleton (n : Int) :
  between_extremes [n] = 0 :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval between_extremes [1, 1]

/-
info: 2
-/
-- #guard_msgs in
-- #eval between_extremes [1, -1]

/-
info: 42
-/
-- #guard_msgs in
-- #eval between_extremes [21, 34, 54, 43, 26, 12]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible