-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bits_battle (nums: List Nat) : String := sorry

theorem bits_battle_output_valid (nums: List Nat) :
  bits_battle nums = "odds win" ∨ 
  bits_battle nums = "evens win" ∨ 
  bits_battle nums = "tie" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_list_tie (nums: List Nat) :
  nums = [] → bits_battle nums = "tie" := sorry

theorem only_odds_result (nums: List Nat) :
  (∀ n ∈ nums, n % 2 = 1) → 
  nums ≠ [] →
  (bits_battle nums = "odds win" ∨ bits_battle nums = "tie") := sorry

theorem only_evens_result (nums: List Nat) :
  (∀ n ∈ nums, n % 2 = 0) →
  nums ≠ [] → 
  (bits_battle nums = "evens win" ∨ bits_battle nums = "tie") := sorry

theorem symmetry_property (nums: List Nat) :
  bits_battle nums = bits_battle nums.reverse := sorry
-- </vc-theorems>