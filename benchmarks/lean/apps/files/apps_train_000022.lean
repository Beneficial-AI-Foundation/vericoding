-- <vc-preamble>
def calc_seq (a k : Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hasZeroDigit (n : Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calc_seq_basic_properties {a k : Nat} (ha : a > 0) (hk : k > 0) :
  let result := calc_seq a k
  -- Result is always non-negative
  result ≥ 0 ∧ 
  -- k=1 returns original number
  calc_seq a 1 = a ∧
  -- k>1 implies result >= input
  (k > 1 → result ≥ a) :=
  sorry

/-
info: 42
-/
-- #guard_msgs in
-- #eval calc_seq 1 4

/-
info: 487
-/
-- #guard_msgs in
-- #eval calc_seq 487 1

/-
info: 628
-/
-- #guard_msgs in
-- #eval calc_seq 487 7
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible