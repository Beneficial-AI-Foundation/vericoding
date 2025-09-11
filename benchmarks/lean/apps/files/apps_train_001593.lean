-- <vc-preamble>
def solution (xs : List Int) : String := sorry

theorem solution_empty_list : solution [] = "" := by sorry

def parseAsInt (s : String) : Option Int := sorry

inductive ValidPart : Type where
  | empty : ValidPart
  | single (n : Int) : ValidPart
  | range (s e : Int) (h : s < e) : ValidPart
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isValidPart (s : String) : Bool := sorry 

theorem solution_valid_parts (xs : List Int) :
  ∀ p ∈ (solution xs).splitOn ",", isValidPart p = true := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solution_nonempty_input (xs : List Int) (h : xs ≠ []) :
  solution xs ≠ "" := by sorry

/-
info: '-6,-3-1,3-5,7-11,14,15,17-20'
-/
-- #guard_msgs in
-- #eval solution [-6, -3, -2, -1, 0, 1, 3, 4, 5, 7, 8, 9, 10, 11, 14, 15, 17, 18, 19, 20]

/-
info: '-3--1,2,10,15,16,18-20'
-/
-- #guard_msgs in
-- #eval solution [-3, -2, -1, 2, 10, 15, 16, 18, 19, 20]

/-
info: '1-5'
-/
-- #guard_msgs in
-- #eval solution [1, 2, 3, 4, 5]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded