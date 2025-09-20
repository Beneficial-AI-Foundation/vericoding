-- <vc-preamble>
def List.maximum' : List Int → Int
  | [] => 0 
  | [x] => x
  | (x::xs) => max x (List.maximum' xs)

def List.Sorted : List Int → Prop := List.Pairwise (· ≤ ·)

def partitioned_at (p : Nat) (nums : List Int) : Prop :=
  let left := (nums.take p)
  let right := (nums.drop p)
  let left_max := List.maximum' left
  (∀ x ∈ left, x ≤ left_max) ∧
  (∀ x ∈ right, x ≥ left_max)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def partition_disjoint (nums : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>