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
-- LLM HELPER: Base case lemma
lemma MaxValueUpToIndex_zero (S : String) : MaxValueUpToIndex S 0 = 0 := by
  unfold MaxValueUpToIndex
  simp

-- LLM HELPER: Lemma showing MaxValue is always non-negative
lemma MaxValue_nonneg (S : String) : MaxValue S ≥ 0 := by
  unfold MaxValue
  -- Prove by strong induction on S.length
  induction' S.length using Nat.strong_induction_on with n ih
  cases' n with n
  · -- Base case: length 0
    simp [MaxValueUpToIndex_zero]
  · -- Inductive case: length n+1
    unfold MaxValueUpToIndex
    simp
    -- The definition gives us: if n + 1 = 0 then 0 else ...
    -- Since n + 1 ≠ 0, we go to the else branch
    have h_nonzero : n + 1 ≠ 0 := Nat.succ_ne_zero n
    simp
    -- Now we have if-then-else, need case analysis
    have ih_applied : MaxValueUpToIndex S n ≥ 0 := by
      apply ih n (Nat.lt_succ_self n)
    -- Case analysis on the condition
    split_ifs with h_cond
    · -- Case: MaxValueUpToIndex S n < CurrentValueAtIndex S (n + 1)
      -- Need to show CurrentValueAtIndex S (n + 1) ≥ 0
      -- Since MaxValueUpToIndex S n ≥ 0 and CurrentValueAtIndex S (n + 1) > MaxValueUpToIndex S n
      linarith [ih_applied, h_cond]
    · -- Case: ¬(MaxValueUpToIndex S n < CurrentValueAtIndex S (n + 1))
      -- Result is MaxValueUpToIndex S n, which is ≥ 0 by IH
      exact ih_applied
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
  unfold solve_postcond solve
  constructor
  · -- Prove result ≥ 0
    apply MaxValue_nonneg
  · -- Prove result = MaxValue S  
    rfl
-- </vc-theorems>
