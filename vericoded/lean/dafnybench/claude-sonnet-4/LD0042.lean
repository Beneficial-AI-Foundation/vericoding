import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: No additional helpers needed for this basic absolute value implementation
-- </vc-helpers>

-- <vc-definitions>
def Abs (x : Int) : Int :=
if x ≥ 0 then x else -x
-- </vc-definitions>

-- <vc-theorems>
theorem Abs_spec (x : Int) :
(x ≥ 0 → Abs x = x) ∧
(x < 0 → x + Abs x = 0) :=
⟨fun h => by simp [Abs, if_pos h], fun h => by simp [Abs, if_neg (not_le.mpr h), add_neg_cancel]⟩
-- </vc-theorems>
