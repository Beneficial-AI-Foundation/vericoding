-- <vc-preamble>
def countOnes (n : Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def shared_bits (a b : Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem shared_bits_symmetric
  {a b : Nat} : shared_bits a b = shared_bits b a := by
  sorry

theorem shared_bits_self
  {x : Nat} : shared_bits x x = (countOnes x > 1) := by
  sorry

theorem shared_bits_and
  {a b : Nat} : shared_bits a b = (countOnes (a &&& b) > 1) := by
  sorry

theorem shared_bits_single_bit
  {x : Nat} (h : x ≤ 1) : shared_bits x x = false := by
  sorry

theorem shared_bits_powers_two
  {p1 p2 : Nat} (h1 : ∃ k1, p1 = 2^k1) (h2 : ∃ k2, p2 = 2^k2) :
  shared_bits p1 p2 = false := by
  sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval shared_bits 1 2

/-
info: False
-/
-- #guard_msgs in
-- #eval shared_bits 7 10

/-
info: True
-/
-- #guard_msgs in
-- #eval shared_bits 7 15
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded