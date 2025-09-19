-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_dist_to_closest : List Nat → Nat := sorry

def List.longestConsecutiveOnes (xs : List Nat) (n : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_dist_non_negative (seats : List Nat) 
  (h : ∃ x ∈ seats, x = 1) :
  max_dist_to_closest seats ≥ 0 := sorry

theorem max_dist_bounded_by_length (seats : List Nat)
  (h : ∃ x ∈ seats, x = 1) :
  max_dist_to_closest seats ≤ seats.length := sorry

theorem max_dist_gap_bound (seats : List Nat) (i j : Nat)
  (h1 : ∃ x ∈ seats, x = 1)
  (h2 : i < seats.length)
  (h3 : j < seats.length) 
  (h4 : seats.get ⟨i, h2⟩ = 1)
  (h5 : seats.get ⟨j, h3⟩ = 1)
  (h6 : i < j) :
  ((j - i - 1) + 1) / 2 ≤ max_dist_to_closest seats := sorry

theorem max_dist_symmetry (seats : List Nat)
  (h : ∃ x ∈ seats, x = 1) :
  max_dist_to_closest seats = max_dist_to_closest seats.reverse := sorry
-- </vc-theorems>