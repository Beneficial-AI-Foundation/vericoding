def valid_suits := ["C", "S", "D", "H"]
def valid_ranks := ["2","3","4","5","6","7","8","9","10","J","Q","K","A"]

-- <vc-helpers>
-- </vc-helpers>

def suit_map := [("C", "clubs"), ("S", "spades"), ("D", "diamonds"), ("H", "hearts")]

def define_suit (card : String) : String :=
  sorry

theorem define_suit_valid (rank : String) (suit : String)
  (h1 : rank ∈ valid_ranks)
  (h2 : suit ∈ valid_suits) :
  ∃ result, result ∈ ["clubs", "spades", "diamonds", "hearts"] ∧
  define_suit (rank ++ suit) = result := 
  sorry

theorem define_suit_invalid (card : String) 
  (h : ∃ rank, rank ∈ valid_ranks ∧ card = rank ++ "X") :
  ¬∃ result, define_suit card = result :=
  sorry

/-
info: 'clubs'
-/
-- #guard_msgs in
-- #eval define_suit "3C"

/-
info: 'spades'
-/
-- #guard_msgs in
-- #eval define_suit "QS"

/-
info: 'hearts'
-/
-- #guard_msgs in
-- #eval define_suit "JH"

-- Apps difficulty: introductory
-- Assurance level: unguarded