-- <vc-preamble>
inductive ValidPart : Type where
  | empty : ValidPart
  | single (n : Int) : ValidPart
  | range (s e : Int) (h : s < e) : ValidPart
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solution (xs : List Int) : String :=
sorry

def parseAsInt (s : String) : Option Int :=
sorry

def isValidPart (s : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solution_empty_list : solution [] = "" := by
sorry

theorem solution_valid_parts (xs : List Int) :
  ∀ p ∈ (solution xs).splitOn ",", isValidPart p = true := by
sorry

theorem solution_nonempty_input (xs : List Int) (h : xs ≠ []) :
  solution xs ≠ "" := by
sorry
-- </vc-theorems>