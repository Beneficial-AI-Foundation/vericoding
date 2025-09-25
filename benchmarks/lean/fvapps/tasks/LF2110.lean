-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_hardness_of_ordering (n : Nat) (positions : List Nat) : List Nat := sorry

def is_valid_permutation (n : Nat) (positions : List Nat) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hardness_list_length {n : Nat} (h : n > 0) 
  (positions : List Nat) (h2 : positions = List.range' 1 n) :
  (find_hardness_of_ordering n positions).length = n + 1 := sorry

theorem first_last_element_one {n : Nat} (h : n > 0) 
  (positions : List Nat) (h2 : is_valid_permutation n positions) :
  let result := find_hardness_of_ordering n positions
  (result.get ⟨0, sorry⟩ = 1) ∧ 
  (result.get ⟨n, sorry⟩ = 1) := sorry

theorem adjacent_diff_at_most_one {n : Nat} (h : n > 0)
  (positions : List Nat) (h2 : is_valid_permutation n positions) :
  let result := find_hardness_of_ordering n positions
  ∀ i, i < result.length - 1 → 
  (result.get ⟨i, sorry⟩).sub (result.get ⟨i+1, sorry⟩) ≤ 1 := sorry

theorem all_values_positive {n : Nat} (h : n > 0)
  (positions : List Nat) (h2 : is_valid_permutation n positions) :
  let result := find_hardness_of_ordering n positions
  ∀ i, i < result.length → result.get ⟨i, sorry⟩ > 0 := sorry

theorem max_value_bounded {n : Nat} (h : n > 0)
  (positions : List Nat) (h2 : is_valid_permutation n positions) :
  let result := find_hardness_of_ordering n positions
  ∀ i, i < result.length → result.get ⟨i, sorry⟩ ≤ n := sorry
-- </vc-theorems>