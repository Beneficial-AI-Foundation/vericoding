import Mathlib
-- <vc-preamble>
instance : DecidablePred (fun n => n ≥ 1) := by infer_instance
instance : DecidablePred (fun n => n ≥ 0) := by infer_instance
instance (n k : Nat) : Decidable (k ≤ n - 1) := by infer_instance

def ValidInput (n m k : Nat) : Prop :=
  n ≥ 1 ∧ m ≥ 1 ∧ k ≥ 0 ∧ k ≤ n - 1

instance (n m k : Nat) : Decidable (ValidInput n m k) := by
  simp [ValidInput]
  infer_instance

def factorial (n : Nat) : Nat :=
  if n = 0 then 1
  else n * factorial (n - 1)

def binomial (n k : Nat) : Nat :=
  if k ≤ n then
    if factorial k = 0 ∨ factorial (n - k) = 0 then 0
    else factorial n / (factorial k * factorial (n - k))
  else 0

def power (base exp : Nat) : Nat :=
  if exp = 0 then 1
  else base * power base (exp - 1)

def ExpectedResult (n m k : Nat) : Nat :=
  if ValidInput n m k then
    (m * power (m - 1) k * binomial (n - 1) k) % 998244353
  else 0

@[reducible, simp]
def solve_precond (n m k : Nat) : Prop :=
  ValidInput n m k
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem primeModPos : 0 < 998244353 := by decide
-- </vc-helpers>

-- <vc-definitions>
def solve (n m k : Nat) (h_precond : solve_precond n m k) : Nat :=
  (m * power (m - 1) k * binomial (n - 1) k) % 998244353
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m k : Nat) (result: Nat) (h_precond : solve_precond n m k) : Prop :=
  result < 998244353

theorem solve_spec_satisfied (n m k : Nat) (h_precond : solve_precond n m k) :
    solve_postcond n m k (solve n m k h_precond) h_precond := by
  simpa [solve_postcond, solve] using
    (Nat.mod_lt (m * power (m - 1) k * binomial (n - 1) k) primeModPos)
-- </vc-theorems>
