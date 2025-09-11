-- <vc-preamble>
def count_char (s : String) (c : Char) : Nat := sorry

def max_removable_steps (n : Nat) (s : String) : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def absDiff (x y : Nat) : Nat := 
  if x ≥ y then x - y else y - x
-- </vc-definitions>

-- <vc-theorems>
theorem max_removable_steps_le_n {n : Nat} {s : String} :
  n > 0 → max_removable_steps n s ≤ n := sorry

theorem max_removable_steps_empty {n : Nat} :
  n > 0 → max_removable_steps n "" = n := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval max_removable_steps 7 "ULUDLLU"

/-
info: 0
-/
-- #guard_msgs in
-- #eval max_removable_steps 4 "RUUR"

/-
info: 4
-/
-- #guard_msgs in
-- #eval max_removable_steps 4 "LRLR"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible