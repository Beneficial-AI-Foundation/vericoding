import Mathlib
-- <vc-preamble>
def ValidInput (n k : Int) : Prop :=
  n ≥ 1 ∧ k ≥ 1 ∧ n ≤ 100 ∧ k ≤ 100

def MinCrackerDifference (n k : Int) : Int :=
  if n % k = 0 then 0 else 1

@[reducible, simp]
def solve_precond (n k : Int) : Prop :=
  ValidInput n k
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: lemmas for modular arithmetic properties
lemma mod_zero_iff_divisible (n k : Int) (hk : k ≠ 0) : n % k = 0 ↔ k ∣ n := by
  exact Int.dvd_iff_emod_eq_zero.symm

lemma k_nonzero_from_precond {n k : Int} (h_precond : solve_precond n k) : k ≠ 0 := by
  unfold solve_precond ValidInput at h_precond
  omega
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (h_precond : solve_precond n k) : Int :=
  MinCrackerDifference n k
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (result: Int) (h_precond : solve_precond n k) : Prop :=
  result = MinCrackerDifference n k ∧ 
  (result = 0 ↔ n % k = 0) ∧ 
  (result = 1 ↔ n % k ≠ 0)

theorem solve_spec_satisfied (n k : Int) (h_precond : solve_precond n k) :
    solve_postcond n k (solve n k h_precond) h_precond := by
  unfold solve_postcond solve MinCrackerDifference
  constructor
  · rfl
  constructor
  · constructor
    · intro h
      -- If result = 0, then (if n % k = 0 then 0 else 1) = 0
      -- This means n % k = 0
      split_ifs at h
      · assumption
      · contradiction
    · intro h
      -- If n % k = 0, then result = 0
      simp [h]
  · constructor
    · intro h
      -- If result = 1, then n % k ≠ 0
      split_ifs at h
      · contradiction
      · assumption
    · intro h
      -- If n % k ≠ 0, then result = 1
      simp [h]
-- </vc-theorems>
