import Mathlib
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
-- LLM HELPER
theorem MaxValueUpToIndex_monotonic (S : String) (k : Nat) :
    MaxValueUpToIndex S k ≤ MaxValueUpToIndex S (k + 1) := by
  conv_rhs => rw [MaxValueUpToIndex]
  simp only [Nat.succ_ne_zero]
  dsimp
  split_ifs with h_gt
  · exact le_of_lt h_gt
  · exact le_refl _

-- LLM HELPER
theorem MaxValueUpToIndex_nonneg (S : String) (n : Nat) : MaxValueUpToIndex S n ≥ 0 := by
  induction n with
  | zero =>
    simp [MaxValueUpToIndex]
  | succ k ih =>
    exact le_trans ih (MaxValueUpToIndex_monotonic S k)
-- </vc-helpers>

-- <vc-definitions>
def solve (N : Int) (S : String) (h_precond : solve_precond N S) : Int :=
  MaxValue S
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N : Int) (S : String) (result : Int) (h_precond : solve_precond N S) : Prop :=
  result ≥ 0 ∧ result = MaxValue S

theorem solve_spec_satisfied (N : Int) (S : String) (h_precond : solve_precond N S) :
    solve_postcond N S (solve N S h_precond) h_precond := by
  dsimp [solve, solve_postcond]
  constructor
  · dsimp [MaxValue]
    apply MaxValueUpToIndex_nonneg
  · rfl
-- </vc-theorems>
