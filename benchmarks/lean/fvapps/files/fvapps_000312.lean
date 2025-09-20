-- <vc-preamble>
def maxList : List Nat → Nat
  | [] => 0
  | (x::xs) => max x (maxList xs)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minOperations (nums : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem minOperations_nonnegative (nums : List Nat) :
  minOperations nums ≥ 0 :=
sorry

theorem minOperations_at_least_nonzero_count (nums : List Nat) :
  minOperations nums ≥ (nums.filter (λ x => x > 0)).length :=
sorry

theorem minOperations_at_least_max_bits (nums : List Nat) :
  nums.length > 0 → nums ≠ [] →
  minOperations nums ≥ (String.length (toString (maxList nums))).pred :=
sorry

theorem minOperations_all_zeros (nums : List Nat) :
  (∀ x ∈ nums, x = 0) → minOperations nums = 0 :=
sorry

theorem minOperations_nonzero_lower_bound (nums : List Nat) :
  (∀ x ∈ nums, x > 0) → minOperations nums ≥ nums.length :=
sorry

theorem minOperations_powers_two_bound (nums : List Nat) (max : Nat) :
  nums.length > 0 →
  (∀ x ∈ nums, ∃ n, x = 2^n) →
  max = maxList nums →
  minOperations nums ≤ (String.length (toString max)) + nums.length :=
sorry
-- </vc-theorems>