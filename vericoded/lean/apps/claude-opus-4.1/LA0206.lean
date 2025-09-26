import Mathlib
-- <vc-preamble>
def IntToString (n : Int) : String :=
  sorry

def ReverseString (s : String) : String :=
  sorry

def StringToInt (s : String) : Int :=
  sorry

def SumOfPalindromes (k : Int) : Int :=
  sorry

def ValidInput (k p : Int) : Prop :=
  k ≥ 1 ∧ p ≥ 1

@[reducible, simp]
def solve_precond (k p : Int) : Prop :=
  ValidInput k p
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def solve (k p : Int) (h_precond : solve_precond k p) : Int :=
  let sum := SumOfPalindromes k
  sum % p
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (k p : Int) (result : Int) (h_precond : solve_precond k p) : Prop :=
  0 ≤ result ∧ result < p ∧ result = (SumOfPalindromes k) % p

theorem solve_spec_satisfied (k p : Int) (h_precond : solve_precond k p) :
    solve_postcond k p (solve k p h_precond) h_precond := by
  unfold solve_postcond solve
  simp [solve_precond, ValidInput] at h_precond
  have h_k : k ≥ 1 := h_precond.1
  have h_p : p ≥ 1 := h_precond.2
  
  -- The result is SumOfPalindromes k % p by definition
  let result := SumOfPalindromes k % p
  
  -- Need to show: 0 ≤ result ∧ result < p ∧ result = SumOfPalindromes k % p
  constructor
  · -- 0 ≤ result
    apply Int.emod_nonneg
    omega
  constructor
  · -- result < p
    have h_pos : (0 : Int) < p := by omega
    exact Int.emod_lt_of_pos _ h_pos
  · -- result = SumOfPalindromes k % p
    rfl
-- </vc-theorems>
