-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MOD := 1000000007

def solve_yalalovichik (s : String) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_digit_identity (c : Char) (h : c.isDigit) :
  solve_yalalovichik (String.mk [c]) = c.toNat - '0'.toNat := sorry

/-
info: 123231312
-/
-- #guard_msgs in
-- #eval solve_yalalovichik "123"

/-
info: 3443
-/
-- #guard_msgs in
-- #eval solve_yalalovichik "34"

/-
info: 9
-/
-- #guard_msgs in
-- #eval solve_yalalovichik "9"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible