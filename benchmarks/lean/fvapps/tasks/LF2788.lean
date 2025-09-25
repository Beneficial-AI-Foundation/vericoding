-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def factors (n : Nat) : List Nat × List Nat := sorry

theorem factors_returns_two_lists (n : Nat) (h : n > 0) :
  let (sq, cb) := factors n
  ∀ x ∈ sq, n % x^2 = 0 ∧ 
  ∀ x ∈ cb, n % x^3 = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem factors_lists_are_sorted (n : Nat) (h : n > 0) :
  let (sq, cb) := factors n
  (∀ i j, i < j → i < List.length sq → j < List.length sq → 
    sq[i]! ≤ sq[j]!) ∧
  (∀ i j, i < j → i < List.length cb → j < List.length cb → 
    cb[i]! ≤ cb[j]!) := sorry

theorem factors_lists_contain_valid_factors (n : Nat) (h : n > 0) :
  let (sq, cb) := factors n
  (∀ x ∈ sq, x ≥ 2 ∧ n % x^2 = 0) ∧
  (∀ x ∈ cb, x ≥ 2 ∧ n % x^3 = 0) := sorry

theorem cube_factors_subset_of_square_factors (n : Nat) (h : n > 0) :
  let (sq, cb) := factors n
  ∀ x ∈ cb, x ∈ sq := sorry
-- </vc-theorems>