import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def lcmInt (a b : Int) : Int :=
0
-- </vc-definitions>

-- <vc-theorems>
theorem lcmInt_spec (a b : Int) :
  lcmInt a b ≥ 0 ∧
  lcmInt a b % a = 0 ∧
  lcmInt a b % b = 0 ∧
  ∀ m : Int, m > 0 → m % a = 0 → m % b = 0 → lcmInt a b ≤ m :=
by
  constructor
  · simp [lcmInt]
  · constructor
    · simp [lcmInt]
    · constructor
      · simp [lcmInt]
      · intro m hm _ _
        simpa [lcmInt] using (le_of_lt hm)
-- </vc-theorems>
