-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_seats (n : Nat) : List Nat := sorry

def will_indulge (a b : Nat) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_seats_length (n : Nat) (h : n > 0) (h2 : n ≤ 100) : 
  (solve_seats n).length = n := sorry

theorem solve_seats_even_numbers (n : Nat) (h : n > 0) (h2 : n ≤ 100) :
  ∀ x ∈ solve_seats n, x % 2 = 0 := sorry

theorem solve_seats_descending (n : Nat) (h : n > 0) (h2 : n ≤ 100) :
  ∀ i j, i < j → j < (solve_seats n).length → 
    (solve_seats n).get ⟨i, sorry⟩ ≥ (solve_seats n).get ⟨j, sorry⟩ := sorry

theorem solve_seats_no_indulging (n : Nat) (h : n > 0) (h2 : n ≤ 20) :
  ∀ i j, i < j → j < (solve_seats n).length → 
    ¬(will_indulge ((solve_seats n).get ⟨i, sorry⟩) ((solve_seats n).get ⟨j, sorry⟩)) := sorry

theorem solve_seats_positive (n : Nat) (h : n > 0) (h2 : n ≤ 100) :
  ∀ x ∈ solve_seats n, x > 0 := sorry
-- </vc-theorems>