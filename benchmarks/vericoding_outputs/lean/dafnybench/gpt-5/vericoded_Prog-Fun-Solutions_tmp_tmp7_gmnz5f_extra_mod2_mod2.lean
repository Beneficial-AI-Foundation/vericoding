import Mathlib
-- <vc-preamble>
def f2 (n : Nat) : Nat :=
if n = 0 then 0
else 5 * f2 (n / 3) + n % 4
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma f2_zero : f2 0 = 0 := by
  simpa [f2]
-- </vc-helpers>

-- <vc-definitions>
def mod2 (n : Nat) : Nat :=
f2 n
-- </vc-definitions>

-- <vc-theorems>
theorem mod2_spec (n : Nat) : mod2 n = f2 n :=
rfl
-- </vc-theorems>
