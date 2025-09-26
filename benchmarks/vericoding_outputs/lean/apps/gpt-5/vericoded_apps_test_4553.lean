import Mathlib
-- <vc-preamble>
def ValidPostalCode (A B : Int) (S : String) : Prop :=
  A ≥ 1 ∧ B ≥ 1 ∧ A ≤ 5 ∧ B ≤ 5 ∧
  S.length = A.natAbs + B.natAbs + 1 ∧
  (∀ i : Nat, i < S.length → (S.data[i]! = '-' ∨ ('0' ≤ S.data[i]! ∧ S.data[i]! ≤ '9'))) ∧
  S.data[A.natAbs]! = '-' ∧ (∀ i : Nat, i < S.length ∧ i ≠ A.natAbs → S.data[i]! ≠ '-')

@[reducible, simp]
def solve_precond (A B : Int) (S : String) : Prop :=
  A ≥ 1 ∧ B ≥ 1 ∧
  A ≤ 5 ∧ B ≤ 5 ∧
  S.length = A.natAbs + B.natAbs + 1 ∧
  (∀ i : Nat, i < S.length → (S.data[i]! = '-' ∨ ('0' ≤ S.data[i]! ∧ S.data[i]! ≤ '9')))
-- </vc-preamble>

-- <vc-helpers>
noncomputable section
-- LLM HELPER
theorem if_yes_no_cases {p : Prop} [Decidable p] :
    ((if p then "Yes" else "No") = "Yes" ∨ (if p then "Yes" else "No") = "No") := by
  by_cases h : p
  · simp [h]
  · simp [h]

-- LLM HELPER
@[simp] theorem if_yes_eq_iff {p : Prop} [Decidable p] :
    ((if p then "Yes" else "No") = "Yes" ↔ p) := by
  by_cases h : p
  · simp [h]
  · simp [h]

-- </vc-helpers>

-- <vc-definitions>
def solve (A B : Int) (S : String) (h_precond : solve_precond A B S) : String :=
  by
  classical
  exact if ValidPostalCode A B S then "Yes" else "No"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (A B : Int) (S : String) (result : String) (h_precond : solve_precond A B S) : Prop :=
  (result = "Yes" ∨ result = "No") ∧
  (result = "Yes" ↔ ValidPostalCode A B S)

theorem solve_spec_satisfied (A B : Int) (S : String) (h_precond : solve_precond A B S) :
    solve_postcond A B S (solve A B S h_precond) h_precond := by
    classical
  dsimp [solve_postcond]
  refine And.intro ?h1 ?h2
  · simpa [solve] using (if_yes_no_cases (p := ValidPostalCode A B S))
  · simpa [solve] using (if_yes_eq_iff (p := ValidPostalCode A B S))
-- </vc-theorems>
