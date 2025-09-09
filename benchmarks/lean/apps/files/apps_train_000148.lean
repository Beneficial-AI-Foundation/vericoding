def partition_disjoint (nums : List Int) : Nat :=
  sorry

axiom List.maximum' : List Int → Int
axiom List.Sorted : List Int → Prop

-- <vc-helpers>
-- </vc-helpers>

def partitioned_at (p : Nat) (nums : List Int) : Prop :=
  let left := (nums.take p)
  let right := (nums.drop p)  
  let left_max := List.maximum' left
  (∀ x ∈ left, x ≤ left_max) ∧ 
  (∀ x ∈ right, x ≥ left_max)

theorem partition_point_valid : ∀ nums, nums.length ≥ 2 →
  let res := partition_disjoint nums
  1 ≤ res ∧ res ≤ nums.length :=
  sorry

theorem partition_left_properties : ∀ nums, nums.length ≥ 2 →
  let res := partition_disjoint nums
  let left := nums.take res
  let left_max := List.maximum' left
  ∀ x ∈ left, x ≤ left_max :=
  sorry

theorem partition_right_properties : ∀ nums, nums.length ≥ 2 →
  let res := partition_disjoint nums
  let left := nums.take res
  let right := nums.drop res
  let left_max := List.maximum' left
  ∀ x ∈ right, x ≥ left_max :=
  sorry

theorem sorted_list_partitions_at_one : ∀ nums, nums.length ≥ 2 →
  List.Sorted nums →
  partition_disjoint nums = 1 :=
  sorry

theorem no_smaller_elements_after_partition : ∀ nums, nums.length ≥ 2 →
  let res := partition_disjoint nums
  let left := nums.take res
  let right := nums.drop res
  let left_max := List.maximum' left
  ¬∃ x ∈ right, x < left_max :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval partition_disjoint [5, 0, 3, 8, 6]

/-
info: 4
-/
-- #guard_msgs in
-- #eval partition_disjoint [1, 1, 1, 0, 6, 12]

/-
info: 3
-/
-- #guard_msgs in
-- #eval partition_disjoint [3, 1, 2, 4, 5]

-- Apps difficulty: interview
-- Assurance level: unguarded