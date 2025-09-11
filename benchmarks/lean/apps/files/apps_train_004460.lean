-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def remainder (dividend divisor : Nat) : Nat := sorry

theorem remainder_properties {dividend divisor : Nat} (h : divisor > 0) : 
  let r := remainder dividend divisor
  (r ≥ 0) ∧ 
  (r < divisor) ∧ 
  (dividend = (dividend / divisor) * divisor + r)
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem remainder_matches_modulo {dividend divisor : Nat} (h : divisor > 0) :
  remainder dividend divisor = dividend % divisor := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval remainder 3 2

/-
info: 1
-/
-- #guard_msgs in
-- #eval remainder 19 2

/-
info: 2
-/
-- #guard_msgs in
-- #eval remainder 27 5
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible