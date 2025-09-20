-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_uncle_johny_position (n : Nat) (nums : List Nat) (k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_uncle_johny_position_smaller_count
  {n : Nat} {nums : List Nat} {k : Nat}
  (h_k : k ≤ nums.length)
  (h_k_pos : k > 0) :
  let target := nums[k-1]'(by
    have h1 : k - 1 < k := by exact Nat.sub_lt (Nat.zero_lt_of_lt h_k_pos) (by decide)
    have h2 : k ≤ nums.length := h_k
    exact Nat.lt_of_lt_of_le h1 h2)
  let smaller_count := (nums.filter (· < target)).length
  find_uncle_johny_position n nums k = smaller_count + 1 :=
sorry
-- </vc-theorems>