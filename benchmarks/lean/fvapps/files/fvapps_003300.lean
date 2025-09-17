-- <vc-preamble>
def unlucky_number (n : Nat) : Nat :=
  sorry

def containsChar (s : String) (c : Char) : Bool :=
  s.any (fun x => x == c)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isDivisibleBy13AndNoUnluckyDigits (i : Nat) : Bool :=
  i % 13 == 0 && 
  !containsChar (toString i) '4' && 
  !containsChar (toString i) '7'
-- </vc-definitions>

-- <vc-theorems>
theorem unlucky_number_non_negative (n : Nat) :
  unlucky_number n ≥ 0 :=
  sorry

theorem unlucky_number_zero :
  unlucky_number 0 = 1 :=
  sorry

theorem unlucky_number_twelve :
  unlucky_number 12 = 1 :=
  sorry

theorem unlucky_number_thirteen :
  unlucky_number 13 = 2 :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval unlucky_number 20

/-
info: 7
-/
-- #guard_msgs in
-- #eval unlucky_number 100

/-
info: 40
-/
-- #guard_msgs in
-- #eval unlucky_number 1000
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible