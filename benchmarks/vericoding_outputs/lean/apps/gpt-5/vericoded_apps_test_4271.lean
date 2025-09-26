import Mathlib
-- <vc-preamble>
def ValidInput (N : Int) (A B C : List Int) : Prop :=
  N ≥ 1 ∧
  A.length = N.natAbs ∧
  B.length = N.natAbs ∧
  C.length = (N - 1).natAbs ∧
  (∀ i, 0 ≤ i ∧ i < N → ∃ h : i.natAbs < A.length, 1 ≤ A[i.natAbs] ∧ A[i.natAbs] ≤ N) ∧
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < N → ∃ hi : i.natAbs < A.length, ∃ hj : j.natAbs < A.length, A[i.natAbs] ≠ A[j.natAbs])

def SumSatisfactionUpTo (A B C : List Int) (k : Nat) : Int :=
  if k = 0 then 0
  else
    let prevSum := SumSatisfactionUpTo A B C (k - 1)
    let baseContrib := if k > 0 ∧ (A[k - 1]! - 1).natAbs < B.length then B[(A[k - 1]! - 1).natAbs]! else 0
    let bonusContrib := if k > 1 ∧ A[k - 1]! = A[k - 2]! + 1 then 
                          if (A[k - 1]! - 2).natAbs < C.length then C[(A[k - 1]! - 2).natAbs]! else 0 
                        else 0
    prevSum + baseContrib + bonusContrib

def SumSatisfaction (A B C : List Int) (N : Int) : Int :=
  if N ≥ 0 then SumSatisfactionUpTo A B C N.natAbs else 0

@[reducible, simp]
def solve_precond (N : Int) (A B C : List Int) : Prop :=
  ValidInput N A B C
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
namespace VCHelpers
end VCHelpers
-- </vc-helpers>

-- <vc-definitions>
def solve (N : Int) (A B C : List Int) (h_precond : solve_precond N A B C) : Int :=
  SumSatisfaction A B C N
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N : Int) (A B C : List Int) (result : Int) (h_precond : solve_precond N A B C) : Prop :=
  result = SumSatisfaction A B C N

theorem solve_spec_satisfied (N : Int) (A B C : List Int) (h_precond : solve_precond N A B C) :
    solve_postcond N A B C (solve N A B C h_precond) h_precond := by
  simp [solve_postcond, solve]
-- </vc-theorems>
