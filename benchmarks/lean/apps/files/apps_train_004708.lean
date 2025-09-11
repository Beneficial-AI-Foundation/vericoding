-- <vc-preamble>
def Card := List (List (Option Nat))
def CalledNumber := String

def bingo (card : Card) (numbers : List CalledNumber) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cardNumberToString (n : Option Nat) : CalledNumber :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bingo_returns_boolean (card : Card) (numbers : List CalledNumber) :
  ∃ b : Bool, bingo card numbers = b :=
  sorry

theorem free_space_is_center (card : Card) : 
  card.get? 2 >>= (·.get? 2) = some none :=
  sorry

theorem empty_calls_no_bingo (card : Card) :
  ¬(bingo card []) :=
  sorry

theorem all_numbers_called_is_bingo (card : Card) (numbers : List CalledNumber) 
  (h : ∀ (i j : Nat), i < card.length → j < (card.get! i).length → 
       (card.get! i).get! j ≠ none → 
       cardNumberToString ((card.get! i).get! j) ∈ numbers) :
  bingo card numbers :=
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval bingo [["B", "I", "N", "G", "O"], [1, 16, 31, 46, 61], [3, 18, 33, 48, 63], [5, 20, "FREE SPACE", 50, 65], [7, 22, 37, 52, 67], [9, 24, 39, 54, 69]] ["B1", "I16", "N31", "G46", "O61"]

/-
info: False
-/
-- #guard_msgs in
-- #eval bingo [["B", "I", "N", "G", "O"], [1, 16, 31, 46, 61], [3, 18, 33, 48, 63], [5, 20, "FREE SPACE", 50, 65], [7, 22, 37, 52, 67], [9, 24, 39, 54, 69]] ["B1", "I16", "N31", "G46"]

/-
info: True
-/
-- #guard_msgs in
-- #eval bingo [["B", "I", "N", "G", "O"], [1, 16, 31, 46, 61], [3, 18, 33, 48, 63], [5, 20, "FREE SPACE", 50, 65], [7, 22, 37, 52, 67], [9, 24, 39, 54, 69]] ["N31", "N33", "N37", "N39"]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded