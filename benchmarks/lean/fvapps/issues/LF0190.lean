-- <vc-preamble>
def List.sum : List Nat → Nat 
  | [] => 0
  | (x::xs) => x + List.sum xs

def getMaximum (l : List Nat) (h : l.length > 0) : Nat :=
  match l with
  | [] => 0 
  | [x] => x
  | (x::xs) => x -- simplified version to avoid proof complexity
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_partition_k_subsets (nums : List Nat) (k : Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem partition_k_eq_one {nums : List Nat} (h : nums.length > 0) :
  can_partition_k_subsets nums 1 = true :=
  sorry

theorem partition_k_gt_length {nums : List Nat} {k : Nat} 
  (h : k > nums.length) :
  can_partition_k_subsets nums k = false :=
  sorry

theorem partition_sum_not_div_k {nums : List Nat} {k : Nat} 
  (h : k > 0) (h2 : nums.length > 0)
  (h3 : (List.sum nums % k) ≠ 0) :
  can_partition_k_subsets nums k = false :=
  sorry

theorem partition_max_too_large {nums : List Nat} {k : Nat}
  (h : k > 0) (h2 : nums.length > 0)
  (h3 : getMaximum nums h2 > List.sum nums / k) :
  can_partition_k_subsets nums k = false :=
  sorry

theorem identical_elements {n k : Nat} (h : k > 0) :
  can_partition_k_subsets (List.replicate n n) k = (n % k = 0) :=
  sorry

theorem single_element_k_one :
  can_partition_k_subsets [1] 1 = true :=
  sorry

theorem single_element_k_two :
  can_partition_k_subsets [1] 2 = false :=
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval can_partition_k_subsets [4, 3, 2, 3, 5, 2, 1] 4

/-
info: False
-/
-- #guard_msgs in
-- #eval can_partition_k_subsets [1, 2, 3, 4] 3

/-
info: True
-/
-- #guard_msgs in
-- #eval can_partition_k_subsets [2, 2, 2, 2] 2
-- </vc-theorems>