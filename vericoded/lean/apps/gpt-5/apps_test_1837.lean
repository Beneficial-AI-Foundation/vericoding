import Mathlib
-- <vc-preamble>
def ValidInput (n: Nat) (A: List Int) : Prop :=
  n ≥ 1 ∧
  A.length = n ∧
  (∀ i, i < n → 0 ≤ A.get! i ∧ A.get! i < (n : Int)) ∧
  (∀ i j, i < j ∧ j < n → A.get! i ≠ A.get! j) ∧
  (∀ k, k < n → ∃ i, i < n ∧ A.get! i = (k : Int))

def CurrentFixedPoints (A: List Int) : Nat :=
  (List.range A.length).filter (fun i => A.get! i = (i : Int)) |>.length

def MaxPossibleFixedPoints (A: List Int) : Nat :=
  let current := CurrentFixedPoints A
  if current = A.length then 
    A.length
  else if ∃ i, i < A.length ∧ A.get! i ≠ (i : Int) ∧ 
            A.get! i ≥ 0 ∧ A.get! i < (A.length : Int) ∧ 
            A.get! (A.get! i).natAbs = (i : Int) then
    current + 2
  else
    current + 1

@[reducible, simp]
def solve_precond (n : Nat) (A : List Int) : Prop :=
  ValidInput n A
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem solve_precond_iff (n : Nat) (A : List Int) : solve_precond n A ↔ ValidInput n A := Iff.rfl

-- LLM HELPER
@[simp] lemma nat_ge_zero (x : Nat) : x ≥ 0 := by simpa using (Nat.zero_le x)
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) (A : List Int) (h_precond : solve_precond n A) : Nat :=
  MaxPossibleFixedPoints A
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Nat) (A : List Int) (result: Nat) (h_precond : solve_precond n A) : Prop :=
  result = MaxPossibleFixedPoints A ∧ result ≥ 0

theorem solve_spec_satisfied (n : Nat) (A : List Int) (h_precond : solve_precond n A) :
    solve_postcond n A (solve n A h_precond) h_precond := by
  unfold solve_postcond
  constructor
  · simp [solve]
  · exact Nat.zero_le _
-- </vc-theorems>
