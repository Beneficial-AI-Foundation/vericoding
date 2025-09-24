-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def canPartition (nums : List Nat) : Bool := sorry

def List.sum : List Nat → Nat 
  | [] => 0
  | x::xs => x + List.sum xs
-- </vc-definitions>

-- <vc-theorems>
theorem canPartition_returns_bool (nums : List Nat) :
  canPartition nums = true ∨ canPartition nums = false :=
sorry

theorem canPartition_odd_sum_false (nums : List Nat) :
  (List.sum nums % 2 ≠ 0) → canPartition nums = false :=
sorry 

theorem canPartition_same_nums_even_length (n : Nat) (len : Nat) :
  len % 2 = 0 →
  canPartition (List.replicate len n) = true :=
sorry

theorem canPartition_singleton_false (n : Nat) :
  canPartition [n] = false :=
sorry

theorem canPartition_pair_same_true (n : Nat) :
  canPartition [n, n] = true :=
sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval can_partition [1, 5, 5, 11]

/-
info: False
-/
-- #guard_msgs in
-- #eval can_partition [1, 2, 3, 5]

/-
info: True
-/
-- #guard_msgs in
-- #eval can_partition [2, 2, 2, 2]
-- </vc-theorems>