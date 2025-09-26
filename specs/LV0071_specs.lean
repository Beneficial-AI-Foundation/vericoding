-- <vc-preamble>
@[reducible, simp]
def singleDigitPrimeFactor_precond (n : Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def singleDigitPrimeFactor (n : Nat) (h_precond : singleDigitPrimeFactor_precond (n)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def singleDigitPrimeFactor_postcond (n : Nat) (result: Nat) (h_precond : singleDigitPrimeFactor_precond (n)) : Prop :=
  result ∈ [0, 2, 3, 5, 7] ∧
  (result = 0 → (n = 0 ∨ [2, 3, 5, 7].all (n % · ≠ 0))) ∧
  (result ≠ 0 → n ≠ 0 ∧ n % result == 0 ∧ (List.range result).all (fun x => x ∈ [2, 3, 5, 7] → n % x ≠ 0))

theorem singleDigitPrimeFactor_spec_satisfied (n: Nat) (h_precond : singleDigitPrimeFactor_precond (n)) :
    singleDigitPrimeFactor_postcond (n) (singleDigitPrimeFactor (n) h_precond) h_precond := by
  sorry
-- </vc-theorems>