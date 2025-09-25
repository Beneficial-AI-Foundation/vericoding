-- <vc-preamble>
def CurrentValueAtIndex (S : String) (index : Nat) : Int :=
  if index = 0 then 0
  else CurrentValueAtIndex S (index - 1) + (if S.get! ⟨index - 1⟩ = 'I' then 1 else -1)
termination_by index

def MaxValueUpToIndex (S : String) (upTo : Nat) : Int :=
  if upTo = 0 then 0
  else 
    let currentValue := CurrentValueAtIndex S upTo
    let maxBefore := MaxValueUpToIndex S (upTo - 1)
    if currentValue > maxBefore then currentValue else maxBefore
termination_by upTo

def MaxValue (S : String) : Int :=
  MaxValueUpToIndex S S.length

@[reducible, simp]
def solve_precond (N : Int) (S : String) : Prop :=
  1 ≤ N ∧ N ≤ 100 ∧ N = S.length ∧ ∀ i : Nat, i < S.length → S.get! ⟨i⟩ = 'I' ∨ S.get! ⟨i⟩ = 'D'
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (N : Int) (S : String) (h_precond : solve_precond N S) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N : Int) (S : String) (result : Int) (h_precond : solve_precond N S) : Prop :=
  result ≥ 0 ∧ result = MaxValue S

theorem solve_spec_satisfied (N : Int) (S : String) (h_precond : solve_precond N S) :
    solve_postcond N S (solve N S h_precond) h_precond := by
  sorry
-- </vc-theorems>