-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def num_triplets (nums1 : List Nat) (nums2 : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem num_triplets_nonnegative (nums1 nums2 : List Nat) : 
  num_triplets nums1 nums2 ≥ 0 :=
  sorry

theorem num_triplets_symmetric (nums1 nums2 : List Nat) :
  num_triplets nums1 nums2 = num_triplets nums2 nums1 :=
  sorry

theorem num_triplets_empty_first (nums2 : List Nat) :
  num_triplets [] nums2 = 0 :=
  sorry

theorem num_triplets_empty_second (nums1 : List Nat) :
  num_triplets nums1 [] = 0 :=
  sorry
-- </vc-theorems>