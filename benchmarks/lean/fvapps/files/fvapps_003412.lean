-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def plane_seat (s : String) : String := sorry

theorem invalid_letters_return_no_seat (n : Nat) (l : Char)
  (h1 : n ≥ 1 ∧ n ≤ 60)
  (h2 : l ∉ ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'K']) :
  plane_seat (toString n ++ toString l) = "No Seat!!" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_numbers_return_no_seat (n : Nat) (l : Char)
  (h1 : n < 1 ∨ n > 60)
  (h2 : l ∈ ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'K']) :
  plane_seat (toString n ++ toString l) = "No Seat!!" := sorry
-- </vc-theorems>