-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findMedianSortedArrays (nums1 : List Int) (nums2 : List Int) : Float :=
  sorry

def getMedian (l : List Int) : Float :=
  sorry

def mergeSorted (l1 l2 : List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem findMedianSortedArrays_correct (nums1 nums2 : List Int)
  (h : ¬(nums1.length = 0 ∧ nums2.length = 0)) :
  findMedianSortedArrays nums1 nums2 = getMedian (mergeSorted nums1 nums2) := by
  sorry

theorem findMedianSortedArrays_symmetric (nums1 nums2 : List Int)
  (h : ¬(nums1.length = 0 ∧ nums2.length = 0)) :
  findMedianSortedArrays nums1 nums2 = findMedianSortedArrays nums2 nums1 := by
  sorry

theorem findMedianSortedArrays_bounded (nums1 nums2 : List Int)
  (h1 : ∀ x ∈ nums1, -1000 ≤ x ∧ x ≤ 1000)
  (h2 : ∀ x ∈ nums2, -1000 ≤ x ∧ x ≤ 1000)
  (h3 : ¬(nums1.length = 0 ∧ nums2.length = 0)) :
  -1000 ≤ findMedianSortedArrays nums1 nums2 ∧
  findMedianSortedArrays nums1 nums2 ≤ 1000 := by
  sorry
-- </vc-theorems>