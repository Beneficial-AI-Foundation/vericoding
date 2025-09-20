-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def judge_point24 (nums : List Nat) : Bool := sorry

theorem judge_point24_returns_bool (nums : List Nat) (h : nums.length = 4) 
  (h₂ : ∀ n ∈ nums, 1 ≤ n ∧ n ≤ 9) : 
  (judge_point24 nums = true) ∨ (judge_point24 nums = false) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem judge_point24_permutation_invariant (nums₁ nums₂ : List Nat) 
  (h : nums₁.length = 4) (h₂ : nums₂.length = 4)
  (h₃ : ∀ n ∈ nums₁, 1 ≤ n ∧ n ≤ 9) (h₄ : ∀ n ∈ nums₂, 1 ≤ n ∧ n ≤ 9)
  (h₅ : ∀ x, x ∈ nums₁ ↔ x ∈ nums₂) :
  judge_point24 nums₁ = judge_point24 nums₂ := sorry

theorem judge_point24_all_ones_impossible (nums : List Nat) 
  (h : nums.length = 4) (h₂ : ∀ n ∈ nums, n ≤ 1) :
  judge_point24 nums = false := sorry

theorem judge_point24_with_24_and_ones (nums : List Nat)
  (h : nums.length = 4) (h₂ : 24 ∈ nums) 
  (h₃ : (nums.filter (· = 1)).length = 3) :
  judge_point24 nums = true := sorry
-- </vc-theorems>