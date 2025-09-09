-- <vc-helpers>
-- </vc-helpers>

def plane_seat (s : String) : String := sorry

theorem invalid_letters_return_no_seat (n : Nat) (l : Char)
  (h1 : n ≥ 1 ∧ n ≤ 60)
  (h2 : l ∉ ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'K']) :
  plane_seat (toString n ++ toString l) = "No Seat!!" := sorry

theorem invalid_numbers_return_no_seat (n : Nat) (l : Char)
  (h1 : n < 1 ∨ n > 60)
  (h2 : l ∈ ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'K']) :
  plane_seat (toString n ++ toString l) = "No Seat!!" := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible