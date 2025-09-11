-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numSubseq (nums : List Nat) (target : Nat) : Nat := sorry

def minimum (l : List Nat) : Option Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numSubseq_non_negative (nums : List Nat) (target : Nat) :
  target ≥ 2 →
  nums.length ≥ 1 →
  ∀ x ∈ nums, x ≥ 1 ∧ x ≤ 1000 →
  numSubseq nums target ≥ 0 := sorry

theorem numSubseq_modulo_bound (nums : List Nat) (target : Nat) :
  target ≥ 2 →
  nums.length ≥ 1 →
  ∀ x ∈ nums, x ≥ 1 ∧ x ≤ 1000 →
  numSubseq nums target < 10^9 + 7 := sorry

theorem numSubseq_single_element (x : Nat) :
  x ≥ 1 →
  x ≤ 100 →
  numSubseq [x] (x * 3) = if x * 2 ≤ x * 3 then 1 else 0 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval numSubseq [3, 5, 6, 7] 9

/-
info: 6
-/
-- #guard_msgs in
-- #eval numSubseq [3, 3, 6, 8] 10

/-
info: 61
-/
-- #guard_msgs in
-- #eval numSubseq [2, 3, 3, 4, 6, 7] 12
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible