-- <vc-preamble>
def List.sum : List Nat → Nat 
  | [] => 0
  | x::xs => x + xs.sum

def List.prod : List Nat → Nat 
  | [] => 1
  | x::xs => x * xs.prod
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_spec_partition (n k : Nat) (command : String) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_spec_partition_length (n k : Nat) (h : k ≤ n) :
  ∀ command, command = "max" ∨ command = "min" →
    (find_spec_partition n k command).length = k := sorry

theorem find_spec_partition_positive (n k : Nat) (h : k ≤ n) :
  ∀ command, command = "max" ∨ command = "min" →
    ∀ x, x ∈ find_spec_partition n k command → x > 0 := sorry

theorem find_spec_partition_max_diff (n k : Nat) (h : k ≤ n) :
  let result := find_spec_partition n k "max"
  ∀ x y, x ∈ result → y ∈ result → x - y ≤ 1 := sorry

/-
info: [3, 3, 2, 2]
-/
-- #guard_msgs in
-- #eval find_spec_partition 10 4 "max"

/-
info: [7, 1, 1, 1]
-/
-- #guard_msgs in
-- #eval find_spec_partition 10 4 "min"

/-
info: [3, 3, 2]
-/
-- #guard_msgs in
-- #eval find_spec_partition 8 3 "max"
-- </vc-theorems>