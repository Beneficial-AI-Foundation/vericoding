import Mathlib
-- <vc-preamble>
def Power (n : Nat) : Nat :=
if n = 0 then 1 else 2 * Power (n-1)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/-- A helper lemma showing `Power n` is equivalent to `2^n`. -/
theorem Power_eq_pow (n : Nat) : Power n = 2^n := by
  induction n with
  | zero =>
    simp [Power]
  | succ n ih =>
    simp [Power, Nat.succ_sub_one, ih]
    rw [pow_succ]
    ring

-- LLM HELPER
/-- Tail-recursive helper for computing powers of 2. -/
def compute_power_loop (n : Nat) (acc : Nat) : Nat :=
  match n with
  | 0 => acc
  | k + 1 => compute_power_loop k (2 * acc)

-- LLM HELPER
/-- Correctness proof for `compute_power_loop`. -/
theorem compute_power_loop_correct (n : Nat) (acc : Nat) :
    compute_power_loop n acc = acc * 2^n := by
  induction n generalizing acc with
  | zero => 
    simp [compute_power_loop]
  | succ k ih =>
    simp [compute_power_loop, pow_succ]
    rw [ih]
    ring
-- </vc-helpers>

-- <vc-definitions>
def CalcPower (n : Nat) : Nat :=
match n with
| 0 => 0
| k + 1 => CalcPower k + 2

def ComputePower (n : Nat) : Nat :=
compute_power_loop n 1
-- </vc-definitions>

-- <vc-theorems>
theorem CalcPower_spec (n : Nat) : CalcPower n = 2*n :=
by
  induction n with
  | zero =>
    unfold CalcPower
    rfl
  | succ n ih =>
    unfold CalcPower
    rw [ih]
    rw [Nat.mul_succ]

theorem ComputePower_spec (n : Nat) : ComputePower n = Power n :=
by
  unfold ComputePower
  rw [compute_power_loop_correct]
  simp
  rw [Power_eq_pow]
-- </vc-theorems>
