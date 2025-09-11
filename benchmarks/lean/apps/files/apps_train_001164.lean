-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_cost_to_transform (s r : String) : Nat := sorry

def countDiffs (s r : String) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cost_to_self (s : String) :
  min_cost_to_transform s s = 0 := sorry

theorem cost_symmetric (s r : String) :
  min_cost_to_transform s r = min_cost_to_transform r s := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval min_cost_to_transform "adefb" "bdefa"

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_cost_to_transform "abc" "abc"

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_cost_to_transform "abc" "def"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible