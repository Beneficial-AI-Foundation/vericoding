def primePalindrome (n : Nat) : Nat :=
  sorry

def isPalindrome (n : Nat) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def isPrime (n : Nat) : Bool :=
  sorry

theorem primePalindrome_geq_input
  (n : Nat)
  (h1 : n ≥ 2)
  (h2 : n ≤ 19990) :
  primePalindrome n ≥ n :=
sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval primePalindrome 6

/-
info: 11
-/
-- #guard_msgs in
-- #eval primePalindrome 8

/-
info: 101
-/
-- #guard_msgs in
-- #eval primePalindrome 13

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible