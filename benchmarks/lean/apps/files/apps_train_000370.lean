def maxSum (nums1 : List Nat) (nums2 : List Nat) : Nat :=
  sorry

def hasCommonElements (l1 l2 : List Nat) : List Nat :=
  sorry

def sumUniqueElements (l1 l2 : List Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def sumCommonElements (l1 l2 : List Nat) : Nat :=
  sorry

theorem maxsum_positive (nums1 nums2 : List Nat) 
  (h1 : ∀ x ∈ nums1, 1 ≤ x ∧ x ≤ 1000)
  (h2 : ∀ x ∈ nums2, 1 ≤ x ∧ x ≤ 1000)
  (h3 : nums1 ≠ []) (h4 : nums2 ≠ []) :
  maxSum nums1 nums2 ≥ 0 := sorry

theorem maxsum_under_modulo (nums1 nums2 : List Nat)
  (h1 : ∀ x ∈ nums1, 1 ≤ x ∧ x ≤ 1000)
  (h2 : ∀ x ∈ nums2, 1 ≤ x ∧ x ≤ 1000)
  (h3 : nums1 ≠ []) (h4 : nums2 ≠ []) :
  maxSum nums1 nums2 < 10^9 + 7 := sorry

theorem maxsum_lower_bound (nums1 nums2 : List Nat)
  (h1 : ∀ x ∈ nums1, 1 ≤ x ∧ x ≤ 1000)
  (h2 : ∀ x ∈ nums2, 1 ≤ x ∧ x ≤ 1000)
  (h3 : nums1 ≠ []) (h4 : nums2 ≠ []) :
  let common := sumCommonElements nums1 nums2
  let unique1 := sumUniqueElements nums1 nums2
  let unique2 := sumUniqueElements nums2 nums1
  maxSum nums1 nums2 ≥ min (unique1 + common) (unique2 + common) % (10^9 + 7) := sorry

/-
info: 30
-/
-- #guard_msgs in
-- #eval maxSum [2, 4, 5, 8, 10] [4, 6, 8, 9]

/-
info: 109
-/
-- #guard_msgs in
-- #eval maxSum [1, 3, 5, 7, 9] [3, 5, 100]

/-
info: 40
-/
-- #guard_msgs in
-- #eval maxSum [1, 2, 3, 4, 5] [6, 7, 8, 9, 10]

-- Apps difficulty: interview
-- Assurance level: unguarded