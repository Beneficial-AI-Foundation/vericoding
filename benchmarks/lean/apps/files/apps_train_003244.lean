-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solution (nums : List Int) : List Int := sorry

def isSorted (l : List Int) : Bool :=
  match l with
  | [] => true
  | [_] => true
  | x::y::rest => x ≤ y && isSorted (y::rest)
-- </vc-definitions>

-- <vc-theorems>
theorem solution_maintains_elements (nums : List Int) :
  (solution nums).foldl (· + ·) 0 = nums.foldl (· + ·) 0 := sorry

theorem solution_length_preserved (nums : List Int) :
  (solution nums).length = nums.length := sorry

theorem solution_is_sorted (nums : List Int) :
  isSorted (solution nums) = true := sorry

theorem solution_empty : solution [] = [] := sorry

/-
info: [1, 2, 3, 5, 10]
-/
-- #guard_msgs in
-- #eval solution [1, 2, 3, 10, 5]

/-
info: []
-/
-- #guard_msgs in
-- #eval solution []

/-
info: []
-/
-- #guard_msgs in
-- #eval solution None
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded