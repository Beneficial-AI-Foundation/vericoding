-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def code (a b : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem code_non_negative (a b : Nat) :
  0 ≤ code a b := by
  sorry

theorem code_commutative (a b : Nat) :
  code a b = code b a := by
  sorry
-- </vc-theorems>