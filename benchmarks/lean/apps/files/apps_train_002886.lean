-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def abacaba (n : Nat) : Char := sorry

theorem abacaba_is_lowercase (n : Nat) : 
  let result := abacaba n
  97 ≤ result.toNat ∧ result.toNat ≤ 122 := sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible