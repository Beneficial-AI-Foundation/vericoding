import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def Abs (x : Int) : Int :=
if x ≥ 0 then x else -x
-- </vc-definitions>

-- <vc-theorems>
theorem Abs_spec (x : Int) :
(x ≥ 0 → Abs x = x) ∧
(x < 0 → x + Abs x = 0) :=
by
  constructor
  · intro hx
    simp [Abs, hx]
  · intro hx
    have hneg : ¬ x ≥ 0 := by
      have : ¬ 0 ≤ x := not_le_of_gt (by simpa using hx)
      simpa [ge_iff_le] using this
    simpa [Abs, hneg] using add_right_neg_self x
-- </vc-theorems>
