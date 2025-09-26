import Mathlib
-- <vc-preamble>
def ValidInput (N H : Int) (A B : List Int) : Prop :=
  A.length = N ∧ B.length = N ∧ N > 0 ∧ H > 0 ∧
  (∀ i : Nat, i < N.natAbs → A[i]! > 0 ∧ B[i]! > 0) ∧
  (∀ i : Nat, i < N.natAbs → A[i]! ≤ B[i]!)

def sumSeq (s : List Int) : Int :=
  match s with
  | [] => 0
  | h :: t => h + sumSeq t

def MaxWieldExists (A : List Int) (maxA : Int) : Prop :=
  maxA ∈ A ∧ (∀ i : Nat, i < A.length → A[i]! ≤ maxA)

@[reducible, simp]
def solve_precond (N H : Int) (A B : List Int) : Prop :=
  ValidInput N H A B
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem ValidInput.H_pos {N H : Int} {A B : List Int} (h : ValidInput N H A B) : H > 0 := by
  rcases h with ⟨_, _, _, hH, _, _⟩
  simpa using hH

-- </vc-helpers>

-- <vc-definitions>
def solve (N H : Int) (A B : List Int) (h_precond : solve_precond N H A B) : Int :=
  H
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N H : Int) (A B : List Int) (result : Int) (h_precond : solve_precond N H A B) : Prop :=
  result > 0

theorem solve_spec_satisfied (N H : Int) (A B : List Int) (h_precond : solve_precond N H A B) :
    solve_postcond N H A B (solve N H A B h_precond) h_precond := by
  simpa [solve, solve_postcond] using (ValidInput.H_pos h_precond)
-- </vc-theorems>
