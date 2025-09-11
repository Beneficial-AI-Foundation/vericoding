-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_jump (nums : List Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_element_always_true (nums : List Nat) :
  nums.length = 1 → can_jump nums = true :=
  sorry

theorem all_nonzero_jumps_reach_end (nums : List Nat) :
  nums.length > 0 → 
  (∀ i, i < nums.length - 1 → nums[i]! > 0) →
  can_jump nums = true :=
  sorry

theorem zero_at_start_cant_jump (nums : List Nat) :
  nums.length > 1 →
  nums[0]! = 0 →
  can_jump nums = false :=
  sorry

theorem reaching_end_property (nums : List Nat) (i : Nat) :
  i < nums.length - 1 →
  nums[i]! = 0 →
  can_jump nums = true →
  ∃ j, j < i ∧ j + nums[j]! > i :=
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval can_jump [2, 3, 1, 1, 4]

/-
info: False
-/
-- #guard_msgs in
-- #eval can_jump [3, 2, 1, 0, 4]

/-
info: True
-/
-- #guard_msgs in
-- #eval can_jump [0]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded