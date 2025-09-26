import Mathlib
-- <vc-preamble>
def Power (n : Nat) : Nat :=
if n = 0 then 1 else 2 * Power (n - 1)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def ComputePower.loop (n : Nat) (acc : Nat) : Nat :=
  match n with
  | 0 => acc
  | k + 1 => ComputePower.loop k (2 * acc)

@[simp] -- LLM HELPER
theorem loop_spec (n : Nat) (acc : Nat) : ComputePower.loop n acc = acc * Power n := by
  induction n generalizing acc with
  | zero =>
    simp [ComputePower.loop, Power]
  | succ k ih =>
    unfold ComputePower.loop
    unfold Power
    simp
    rw [ih]
    ring

-- </vc-helpers>

-- <vc-definitions>
def ComputePower (n : Nat) : Nat :=
ComputePower.loop n 1
-- </vc-definitions>

-- <vc-theorems>
theorem ComputePower_spec (n : Nat) :
ComputePower n = Power n :=
by
  simp [ComputePower, loop_spec]
-- </vc-theorems>
