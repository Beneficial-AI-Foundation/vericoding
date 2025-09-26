import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Use existing Mathlib lemmas for integer comparison
-- le_or_gt and not_le are already available from Mathlib
-- </vc-helpers>

-- <vc-definitions>
def Min_ (x y : Int) : Int :=
if x ≤ y then x else y
-- </vc-definitions>

-- <vc-theorems>
theorem Min_spec (x y z : Int) :
z = Min_ x y →
((x ≤ y → z = x) ∧
(x > y → z = y)) :=
by
  intro h
  constructor
  · intro hle
    unfold Min_ at h
    simp [hle] at h
    exact h
  · intro hgt
    unfold Min_ at h
    simp [not_le.mpr hgt] at h
    exact h
-- </vc-theorems>
