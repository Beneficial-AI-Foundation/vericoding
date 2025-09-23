-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_dot_product (nums1 nums2 : List Int) : Int := sorry

theorem max_dot_product_bounds 
  (nums1 nums2 : List Int) :
  let min_product := (List.map (fun x => List.map (fun y => x * y) nums2) nums1).join.minimum?
  let max_product := (List.map (fun x => List.map (fun y => x * y) nums2) nums1).join.maximum?
  match min_product, max_product with
  | some min, some max => 
    max_dot_product nums1 nums2 ≥ min ∧ 
    max_dot_product nums1 nums2 ≤ nums1.length * max
  | _, _ => True := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_dot_product_reverse_invariant
  (nums1 nums2 : List Int) :
  max_dot_product nums1 nums2 = max_dot_product nums1.reverse nums2.reverse := sorry

theorem max_dot_product_neg_invariant
  (nums1 nums2 : List Int) :
  max_dot_product nums1 nums2 = 
    - (max_dot_product (nums1.map (fun x => -x)) (nums2.map (fun x => -x))) := sorry

theorem max_dot_product_monotonic
  (nums1 nums2 : List Int) :
  let big_num := max (nums1.maximum?.getD 0) (nums2.maximum?.getD 0) + 100
  max_dot_product (nums1 ++ [big_num]) (nums2 ++ [big_num]) ≥ 
    max_dot_product nums1 nums2 := sorry

/-
info: 18
-/
-- #guard_msgs in
-- #eval max_dot_product [2, 1, -2, 5] [3, 0, -6]

/-
info: 21
-/
-- #guard_msgs in
-- #eval max_dot_product [3, -2] [2, -6, 7]

/-
info: -1
-/
-- #guard_msgs in
-- #eval max_dot_product [-1, -1] [1, 1]
-- </vc-theorems>