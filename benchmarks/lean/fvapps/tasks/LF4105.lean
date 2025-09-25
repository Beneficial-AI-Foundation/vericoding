-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def shortest_arrang (n : Nat) : List Nat := sorry

def is_valid_arrangement (arr : List Nat) (n : Nat) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem shortest_arrang_properties (n : Nat) (h : n ≥ 3) :
  let result := shortest_arrang n
  (result = List.nil ∨ is_valid_arrangement result n) ∧
  (n % 2 = 1 → result = [n/2 + 1, n/2]) := sorry

theorem shortest_arrang_uniqueness (n : Nat) (h : n ≥ 3) :
  let result := shortest_arrang n
  ∀ (i : Nat) (h : i < result.length),
  let test_arr := result
  result ≠ List.nil →
  (test_arr.foldl (· + ·) 0 = n ∧ 
   ∀ j < test_arr.length - 1, 
   test_arr.get ⟨j, sorry⟩ > test_arr.get ⟨j+1, sorry⟩) 
  → False := sorry

theorem powers_of_two_give_empty (n : Nat) :
  (∃ k, n = 2^k) → shortest_arrang n = List.nil := sorry
-- </vc-theorems>