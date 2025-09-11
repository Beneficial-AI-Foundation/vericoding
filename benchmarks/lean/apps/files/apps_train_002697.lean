-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (start offset : Nat) : String := sorry 

theorem solve_single_char_len :
  ∀ (start offset : Nat), offset = 1 → String.length (solve start offset) = 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_start_slice :
  solve 0 3 = "235" := sorry

theorem solve_middle_slice :
  solve 10 5 = "19232" := sorry

theorem solve_longer_slice_len :
  ∀ (start offset : Nat), offset = 10 → start = 100 → String.length (solve start offset) = 10 := sorry

theorem solve_result_properties :
  ∀ (start offset : Nat), start = 50 ∧ offset = 20 → 
    let result := solve start offset
    (∀ c ∈ result.data, '0' ≤ c ∧ c ≤ '9') ∧ (result.length > 0) := sorry

/-
info: '57'
-/
-- #guard_msgs in
-- #eval solve 2 2

/-
info: '19232'
-/
-- #guard_msgs in
-- #eval solve 10 5

/-
info: '192'
-/
-- #guard_msgs in
-- #eval solve 10 3
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded