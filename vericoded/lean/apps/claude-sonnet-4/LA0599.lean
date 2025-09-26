import Mathlib
-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length > 0 ∧ 
  (let s := if input.length > 0 ∧ input.back = '\n' 
            then input.dropRight 1
            else input;
   s = "ABC" ∨ s = "ARC")

def NormalizeInput (input : String) : String :=
  if input.length > 0 ∧ input.back = '\n' 
  then input.dropRight 1
  else input

def ExpectedOutput (input : String) : String :=
  let s := NormalizeInput input;
  if s = "ABC" then "ARC\n" else "ABC\n"

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- Helper lemmas for the solve function
lemma normalize_valid_input (input : String) (h : ValidInput input) : 
    NormalizeInput input = "ABC" ∨ NormalizeInput input = "ARC" := by
  -- From ValidInput, we know input.length > 0 and the normalized string is "ABC" or "ARC"
  have h_len : 0 < input.length := h.1
  have h_norm : (if 0 < input.length ∧ input.back = '\n' then input.dropRight 1 else input) = "ABC" ∨
                (if 0 < input.length ∧ input.back = '\n' then input.dropRight 1 else input) = "ARC" := h.2
  -- Since we know 0 < input.length, we can simplify the conditionals
  simp only [NormalizeInput]
  -- Convert h_norm to use input.length > 0 to match the target
  have h_norm' : (if input.length > 0 ∧ input.back = '\n' then input.dropRight 1 else input) = "ABC" ∨
                 (if input.length > 0 ∧ input.back = '\n' then input.dropRight 1 else input) = "ARC" := by
    -- Use the fact that 0 < input.length is equivalent to input.length > 0
    have : 0 < input.length ↔ input.length > 0 := by simp [Nat.pos_iff_ne_zero]
    simp only [this] at h_norm
    exact h_norm
  exact h_norm'
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  let s := NormalizeInput input
  if s = "ABC" then "ARC\n" else "ABC\n"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result = ExpectedOutput input

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  simp [solve_postcond, solve, ExpectedOutput, NormalizeInput]
-- </vc-theorems>
