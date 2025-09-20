-- <vc-preamble>
def absDiff (x y : Nat) : Nat :=
  if x ≥ y then x - y else y - x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_removable_steps (n : Nat) (s : String) : Nat := sorry

def count_char (s : String) (c : Char) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_removable_steps_le_n {n : Nat} {s : String} :
  n > 0 → max_removable_steps n s ≤ n :=
sorry

theorem max_removable_steps_empty {n : Nat} :
  n > 0 → max_removable_steps n "" = n :=
sorry
-- </vc-theorems>