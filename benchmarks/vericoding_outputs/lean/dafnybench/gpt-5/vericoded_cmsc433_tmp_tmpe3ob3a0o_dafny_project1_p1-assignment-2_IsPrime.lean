import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
noncomputable section
open Classical
-- </vc-helpers>

-- <vc-definitions>
def IsPrime (m : Int) : Bool :=
by
  classical
  exact decide (m > 1 ∧ ∀ j : Int, 2 ≤ j ∧ j < m → m % j ≠ 0)
-- </vc-definitions>

-- <vc-theorems>
theorem IsPrime_spec (m : Int) :
m > 0 →
(IsPrime m ↔ (m > 1 ∧ ∀ j : Int, 2 ≤ j ∧ j < m → m % j ≠ 0)) :=
by
  intro _
  classical
  simp [IsPrime]
-- </vc-theorems>
