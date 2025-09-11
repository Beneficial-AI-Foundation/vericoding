-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gcd (a b : Nat) : Nat := sorry

def fraction (a b : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fraction_output_lower_bound {a b : Nat} (ha : a > 0) (hb : b > 0) :
  fraction a b ≥ 2 := sorry

theorem fraction_identity_cases {n : Nat} (hn : n > 0) :
  fraction n n = 2 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval fraction 2 4

/-
info: 11
-/
-- #guard_msgs in
-- #eval fraction 10 100

/-
info: 2
-/
-- #guard_msgs in
-- #eval fraction 5 5
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible