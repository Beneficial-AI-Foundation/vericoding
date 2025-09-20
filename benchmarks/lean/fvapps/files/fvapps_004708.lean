-- <vc-preamble>
def Card := List (List (Option Nat))
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def CalledNumber := String

def bingo (card : Card) (numbers : List CalledNumber) : Bool :=
  sorry

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
-- </vc-theorems>