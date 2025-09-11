-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bitwiseComplement (n : Nat) : Nat := sorry

theorem complement_range (n : Nat) (h : n ≤ 10^9) : 
  let result := bitwiseComplement n
  0 ≤ result ∧ Nat.log2 result + 1 ≤ Nat.log2 n + 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem complement_bit_flip (n : Nat) (h : n ≤ 10^9) :
  let result := bitwiseComplement n
  ∀ i : Nat, i < Nat.log2 n + 1 → 
    Nat.testBit n i ≠ Nat.testBit result i := sorry

theorem complement_edge_cases :
  bitwiseComplement 0 = 1 ∧ 
  bitwiseComplement 1 = 0 ∧
  bitwiseComplement 2 = 1 := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval bitwiseComplement 5

/-
info: 0
-/
-- #guard_msgs in
-- #eval bitwiseComplement 7

/-
info: 5
-/
-- #guard_msgs in
-- #eval bitwiseComplement 10
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible