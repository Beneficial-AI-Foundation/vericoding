-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fusc (n : Nat) : Nat := sorry

@[simp]
-- </vc-definitions>

-- <vc-theorems>
theorem fusc_zero : fusc 0 = 0 := sorry

@[simp] 

theorem fusc_one : fusc 1 = 1 := sorry

theorem fusc_non_negative (n : Nat) : 
  fusc n ≥ 0 := sorry

theorem fusc_double (n : Nat) :
  fusc (2 * n) = fusc n := sorry 

theorem fusc_odd (n : Nat) :
  fusc (2 * n + 1) = fusc n + fusc (n + 1) := sorry

theorem fusc_consecutive_coprime (n : Nat) :
  Nat.gcd (fusc n) (fusc (n + 1)) = 1 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval fusc 0

/-
info: 1
-/
-- #guard_msgs in
-- #eval fusc 1

/-
info: 21
-/
-- #guard_msgs in
-- #eval fusc 85
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible