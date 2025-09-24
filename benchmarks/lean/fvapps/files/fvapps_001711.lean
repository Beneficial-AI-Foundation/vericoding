-- <vc-preamble>
def Suit := Char
def Card := String
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Hand := List Card

def who_wins_beggar_thy_neighbour (hands : List Hand) (special_cards : String := "JQKA") : Option Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem game_always_terminates
  (hands : List Hand) 
  (h1 : hands.length ≥ 2)
  (h2 : hands.length ≤ 4) :
  match who_wins_beggar_thy_neighbour hands with
  | none => True
  | some n => n ≥ 0 ∧ n < hands.length
  := by sorry

theorem winner_validity 
  (hands : List Hand)
  (special_cards : String)
  (h1 : hands.length ≥ 2)
  (h2 : hands.length ≤ 4) 
  (h3 : ∀ h ∈ hands, h.length > 0)
  (h4 : ∀ c ∈ special_cards.toList, c ∈ ['J', 'Q', 'K', 'A']) :
  match who_wins_beggar_thy_neighbour hands special_cards with
  | none => True
  | some n => n < hands.length
  := by sorry

theorem custom_special_cards
  (hands : List Hand)
  (special_cards : String)
  (h1 : hands.length ≥ 2)
  (h2 : hands.length ≤ 4)
  (h3 : special_cards.length > 0)
  (h4 : special_cards.length ≤ 13)
  (h5 : ∀ c ∈ special_cards.toList, c ∈ ['2', '3', '4', '5', '6', '7', '8', '9', 'T', 'J', 'Q', 'K', 'A']) :
  match who_wins_beggar_thy_neighbour hands special_cards with
  | none => True
  | some n => n ≥ 0 ∧ n < hands.length
  := by sorry
-- </vc-theorems>