import Mathlib
-- <vc-preamble>
def validInput (s : String) : Prop :=
  s.length > 0 ∧ ∀ i, 0 ≤ i ∧ i < s.length → 
    s.data[i]! = ' ' ∨ s.data[i]! = '\n' ∨ ('0' ≤ s.data[i]! ∧ s.data[i]! ≤ '9') ∨ s.data[i]! = '-'

def validNumber (s : String) : Prop :=
  s.length = 0 ∨ ∀ i, 0 ≤ i ∧ i < s.length → 
    ('0' ≤ s.data[i]! ∧ s.data[i]! ≤ '9') ∨ (i = 0 ∧ s.data[i]! = '-')

def countZeros (numbers : List Int) : Int :=
  match numbers with
  | [] => 0
  | x :: xs => (if x = 0 then 1 else 0) + countZeros xs

def findZeroIndex (numbers : List Int) : Int :=
  match numbers with
  | [] => 0
  | x :: xs => if x = 0 then 0 else 1 + findZeroIndex xs

axiom parseInts (s : String) : List Int

axiom generateOutput (numbers : List Int) : String

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  validInput input ∧ input.length > 0
-- </vc-preamble>

-- <vc-helpers>
noncomputable section
-- LLM HELPER
@[simp] lemma solve_precond_left {input : String} (h : solve_precond input) : validInput input := h.left
@[simp] lemma solve_precond_right {input : String} (h : solve_precond input) : input.length > 0 := h.right
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  generateOutput (parseInts input)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  let numbers := parseInts input
  result = generateOutput numbers

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  simp [solve_postcond, solve]
-- </vc-theorems>
