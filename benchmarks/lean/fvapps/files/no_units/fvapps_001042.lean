-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def predict_winner (n : Nat) (nums : List Nat) : String := sorry

theorem predict_winner_valid_output (n : Nat) (nums : List Nat) :
  nums.length > 0 → 
  let result := predict_winner n nums
  result = "Derek" ∨ result = "Henry" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem predict_winner_small_numbers (n : Nat) (nums : List Nat) :
  nums.length > 0 →
  nums.length ≤ 10 →
  (∀ x ∈ nums, x ≤ 5) →
  let result := predict_winner n nums
  result = "Derek" ∨ result = "Henry" := sorry

theorem predict_winner_multiples_of_four (n : Nat) (nums : List Nat) :
  nums.length > 0 →
  nums.length ≤ 100 →
  (∀ x ∈ nums, x % 4 = 0) →
  ∃ result, predict_winner n nums = result := sorry
-- </vc-theorems>