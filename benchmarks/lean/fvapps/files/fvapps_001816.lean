-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSorted (l : List Int) : Bool :=
  sorry

def k_smallest_pairs (nums1 nums2 : List Int) (k : Nat) : List (Int × Int) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem k_smallest_pairs_size (nums1 nums2 : List Int) (k : Nat)
  (h1 : isSorted nums1 = true) (h2 : isSorted nums2 = true) (h3 : nums1 ≠ []) (h4 : nums2 ≠ []) :
  let result := k_smallest_pairs nums1 nums2 k
  List.length result ≤ k ∧ List.length result ≤ List.length nums1 * List.length nums2 :=
sorry

theorem k_smallest_pairs_elements (nums1 nums2 : List Int) (k : Nat)
  (h1 : isSorted nums1 = true) (h2 : isSorted nums2 = true) (h3 : nums1 ≠ []) (h4 : nums2 ≠ []) :
  let result := k_smallest_pairs nums1 nums2 k
  ∀ pair ∈ result, (List.elem pair.1 nums1 ∧ List.elem pair.2 nums2) :=
sorry

theorem k_smallest_pairs_ordered (nums1 nums2 : List Int) (k : Nat)
  (h1 : isSorted nums1 = true) (h2 : isSorted nums2 = true) (h3 : nums1 ≠ []) (h4 : nums2 ≠ []) :
  let result := k_smallest_pairs nums1 nums2 k
  ∀ i, i + 1 < result.length →
    (result.get! i).1 + (result.get! i).2 ≤ (result.get! (i+1)).1 + (result.get! (i+1)).2 :=
sorry

theorem k_smallest_pairs_min_sum (nums1 nums2 : List Int) (k : Nat)
  (h1 : isSorted nums1 = true) (h2 : isSorted nums2 = true) (h3 : nums1 ≠ []) (h4 : nums2 ≠ []) :
  let result := k_smallest_pairs nums1 nums2 k
  result ≠ [] →
    (result.get! 0).1 + (result.get! 0).2 = nums1.get! 0 + nums2.get! 0 :=
sorry

theorem k_smallest_pairs_all_combinations (nums1 nums2 : List Int)
  (h1 : isSorted nums1 = true) (h2 : isSorted nums2 = true) (h3 : nums1 ≠ []) (h4 : nums2 ≠ []) :
  let k := List.length nums1 * List.length nums2
  let result := k_smallest_pairs nums1 nums2 k
  List.length result = k ∧
  ∀ x ∈ nums1, ∀ y ∈ nums2, ∃ pair ∈ result, pair = (x, y) :=
sorry
-- </vc-theorems>