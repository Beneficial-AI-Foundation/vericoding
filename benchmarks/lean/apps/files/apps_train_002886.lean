-- <vc-helpers>
-- </vc-helpers>

def abacaba (n : Nat) : Char := sorry

theorem abacaba_is_lowercase (n : Nat) : 
  let result := abacaba n
  97 ≤ result.toNat ∧ result.toNat ≤ 122 := sorry

/-
info: 'a'
-/
-- #guard_msgs in
-- #eval abacaba 1

/-
info: 'c'
-/
-- #guard_msgs in
-- #eval abacaba 4

/-
info: 'e'
-/
-- #guard_msgs in
-- #eval abacaba 16

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible