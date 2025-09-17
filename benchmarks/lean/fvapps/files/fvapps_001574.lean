-- <vc-preamble>
def countOnes (a b : Nat) : Nat := sorry

def toBinary (n : Nat) : List Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countBinaryOnes (n : Nat) : Nat := sorry

theorem countOnes_non_negative
  (a b : Nat)
  (h1 : 0 < a) (h2 : a ≤ 10^6)
  (h3 : 0 < b) (h4 : b ≤ 10^6) :
  0 ≤ countOnes a b :=
sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: 8
-/
-- #guard_msgs in
-- #eval countOnes 4 7

/-
info: 2
-/
-- #guard_msgs in
-- #eval countOnes 5 5

/-
info: 14846928141
-/
-- #guard_msgs in
-- #eval countOnes 1 1000000000
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible