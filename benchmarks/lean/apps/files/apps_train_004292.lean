-- <vc-helpers>
-- </vc-helpers>

def VALID_CARDS := ["2","3","4","5","6","7","8","9","T","J","Q","K","A"]

def winner (deck1 deck2 : List String) : String :=
  sorry

theorem winner_valid_output (deck1 deck2 : List String) 
  (h1 : ∀ x ∈ deck1, x ∈ VALID_CARDS)
  (h2 : ∀ x ∈ deck2, x ∈ VALID_CARDS)
  (h3 : deck1 ≠ []) 
  (h4 : deck2 ≠ [])
  (h5 : deck1.length = deck2.length) :
  (winner deck1 deck2 = "Steve wins") ∨ 
  (winner deck1 deck2 = "Josh wins") ∨
  (winner deck1 deck2 = "Tie") :=
sorry

theorem winner_symmetry (deck1 deck2 : List String)
  (h1 : ∀ x ∈ deck1, x ∈ VALID_CARDS)
  (h2 : ∀ x ∈ deck2, x ∈ VALID_CARDS)
  (h3 : deck1 ≠ [])
  (h4 : deck2 ≠ [])
  (h5 : deck1.length = deck2.length) :
  (winner deck1 deck2 = "Steve wins" → winner deck2 deck1 = "Josh wins") ∧
  (winner deck1 deck2 = "Josh wins" → winner deck2 deck1 = "Steve wins") ∧
  (winner deck1 deck2 = "Tie" → winner deck2 deck1 = "Tie") :=
sorry

theorem winner_identical_decks (deck : List String)
  (h1 : ∀ x ∈ deck, x ∈ VALID_CARDS)
  (h2 : deck ≠ []) :
  winner deck deck = "Tie" :=
sorry

/-
info: 'Steve wins 2 to 1'
-/
-- #guard_msgs in
-- #eval winner ["A", "7", "8"] ["K", "5", "9"]

/-
info: 'Tie'
-/
-- #guard_msgs in
-- #eval winner ["T"] ["T"]

/-
info: 'Steve wins 1 to 0'
-/
-- #guard_msgs in
-- #eval winner ["T", "9"] ["T", "8"]

-- Apps difficulty: introductory
-- Assurance level: unguarded