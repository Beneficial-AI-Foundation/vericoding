import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma Int.zero_mul' (x : Int) : (0 : Int) * x = 0 := by simpa using (zero_mul x)
@[simp] lemma Int.mul_zero' (x : Int) : x * (0 : Int) = 0 := by simpa using (mul_zero x)
-- </vc-helpers>

-- <vc-definitions>
def DoubleQuadruple (x : Int) : Int × Int :=
(2 * x, 4 * x)
-- </vc-definitions>

-- <vc-theorems>
theorem DoubleQuadruple_spec (x : Int) :
let (a, b) := DoubleQuadruple x
a = 2 * x ∧ b = 4 * x :=
by
  dsimp [DoubleQuadruple]
  exact ⟨rfl, rfl⟩
-- </vc-theorems>
