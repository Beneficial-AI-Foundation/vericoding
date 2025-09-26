import Mathlib
-- <vc-preamble>
def power (x : Float) (n : Nat) : Float :=
match n with
| 0 => 1.0
| n + 1 => x * power x n
-- </vc-preamble>

-- <vc-helpers>

-- LLM HELPER
private def powerLoop (x : Float) (n : Nat) (acc : Float) : Float :=
  match n with
  | 0 => acc
  | k + 1 => powerLoop x k (x * acc)

-- LLM HELPER
private theorem powerLoop_distrib_mul (x : Float) (n : Nat) :
  ∀ (acc : Float), powerLoop x n (x * acc) = x * (powerLoop x n acc) := by
  induction n with
  | zero =>
    intro acc
    simp [powerLoop]
  | succ n' ih =>
    intro acc
    simp only [powerLoop]
    exact ih (x * acc)

-- </vc-helpers>

-- <vc-definitions>
def powerIter (x : Float) (n : Nat) : Float :=
powerLoop x n 1.0
-- </vc-definitions>

-- <vc-theorems>
theorem powerIter_spec (x : Float) (n : Nat) :
powerIter x n = power x n :=
by
  unfold powerIter
  induction n with
  | zero =>
    simp only [powerLoop, power]
  | succ n' ih =>
    simp only [power, powerLoop]
    rw [←ih]
    exact (powerLoop_distrib_mul x n' 1.0)
-- </vc-theorems>
