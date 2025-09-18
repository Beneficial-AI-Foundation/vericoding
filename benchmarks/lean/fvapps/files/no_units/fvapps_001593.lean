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
-- </vc-helpers>

-- <vc-definitions>
def isValidPart (s : String) : Bool := sorry 

theorem solution_valid_parts (xs : List Int) :
  ∀ p ∈ (solution xs).splitOn ",", isValidPart p = true := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solution_nonempty_input (xs : List Int) (h : xs ≠ []) :
  solution xs ≠ "" := by sorry
-- </vc-theorems>