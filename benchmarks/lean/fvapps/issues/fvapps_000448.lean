-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.sum [Add α] (l : List α) : α := sorry 

def minSubarray (nums : List Nat) (p : Nat) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem minSubarray_bounds
  (nums : List Nat)
  (p : Nat)
  (h1 : ∀ n ∈ nums, 1 ≤ n ∧ n ≤ 1000)
  (h2 : 1 ≤ p ∧ p ≤ 1000)
  : -1 ≤ minSubarray nums p ∧ minSubarray nums p ≤ nums.length := sorry 

theorem minSubarray_neg_one_valid
  (nums : List Nat)
  (p : Nat)
  (h : minSubarray nums p = -1)
  : ∀ (i j : Nat), i ≤ nums.length → j ≤ nums.length - i →
    (List.take i nums ++ List.drop (i + j) nums).sum % p ≠ 0 := sorry

theorem minSubarray_zero_valid
  (nums : List Nat) 
  (p : Nat)
  (h : minSubarray nums p = 0)
  : nums.sum % p = 0 := sorry

theorem minSubarray_positive_valid
  (nums : List Nat)
  (p : Nat)
  (h1 : 0 < minSubarray nums p)
  (h2 : minSubarray nums p < nums.length)
  : ∃ (i : Nat), i + (minSubarray nums p).toNat ≤ nums.length ∧ 
    (List.take i nums ++ List.drop (i + (minSubarray nums p).toNat) nums).sum % p = 0 := sorry

theorem minSubarray_small_values
  (nums : List Nat)
  (p : Nat)
  (h1 : ∀ n ∈ nums, 0 ≤ n ∧ n ≤ 10)
  (h2 : 1 ≤ p ∧ p ≤ 10)
  (h3 : minSubarray nums p ≥ 0)
  : ∃ (i : Nat), i + (minSubarray nums p).toNat ≤ nums.length ∧
    (List.take i nums ++ List.drop (i + (minSubarray nums p).toNat) nums).sum % p = 0 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_subarray [3, 1, 4, 2] 6

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_subarray [6, 3, 5, 2] 9

/-
info: -1
-/
-- #guard_msgs in
-- #eval min_subarray [1, 2, 3] 7
-- </vc-theorems>