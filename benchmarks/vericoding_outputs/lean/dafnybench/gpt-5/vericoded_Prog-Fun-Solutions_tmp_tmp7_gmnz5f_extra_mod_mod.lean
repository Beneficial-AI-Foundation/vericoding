import Mathlib
-- <vc-preamble>
def f (n : Nat) : Nat :=
if n = 0 then 1
else if n % 2 = 0 then 1 + 2 * f (n / 2)
else 2 * f (n / 2)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helpers needed for this file.
-- </vc-helpers>

-- <vc-definitions>
def mod (n : Nat) : Nat :=
f n
-- </vc-definitions>

-- <vc-theorems>
theorem mod_spec (n : Nat) : mod n = f n :=
rfl
-- </vc-theorems>
