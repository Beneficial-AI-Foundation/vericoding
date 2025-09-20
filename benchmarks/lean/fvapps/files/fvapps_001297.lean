-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_min_pair_sum (n : Nat) (nums : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_min_pair_sum_is_min_of_two_smallest {n : Nat} {nums : List Int} 
  (h : nums.length = n) (h2 : n ≥ 2) :
  ∃ i j : Nat, i < n ∧ j < n ∧ i < j :=
  sorry

theorem find_min_pair_sum_is_minimal {n : Nat} {nums : List Int} {i j : Nat}
  (h : nums.length = n) (h2 : n ≥ 2) (h3 : i < n) (h4 : j < n) (h5 : i < j) :
  ∃ a b : Int, a + b = find_min_pair_sum n nums ∧ a + b ≤ nums.get ⟨i, by {rw [h]; exact h3}⟩ + nums.get ⟨j, by {rw [h]; exact h4}⟩ :=
  sorry

theorem find_min_pair_sum_errors_empty :
  ∀ l : List Int, l.length = 0 → find_min_pair_sum 0 l = find_min_pair_sum 0 l → False :=
  sorry

theorem find_min_pair_sum_errors_single (x : Int) :
  find_min_pair_sum 1 [x] = find_min_pair_sum 1 [x] → False :=
  sorry
-- </vc-theorems>