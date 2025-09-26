import Mathlib
-- <vc-preamble>
def ValidBinaryString (s : List Char) : Prop :=
  ∀ i, i < s.length → s[i]! = '0' ∨ s[i]! = '1'

def LongestNonDecreasingSubseqHelper (str : List Char) (i : Nat) (currentLen : Nat) (maxLen : Nat) : Nat :=
  if i ≥ str.length then maxLen
  else
    let newCurrentLen := if str[i]! ≥ str[i-1]! then currentLen + 1 else 1
    let newMaxLen := if newCurrentLen > maxLen then newCurrentLen else maxLen
    LongestNonDecreasingSubseqHelper str (i + 1) newCurrentLen newMaxLen

def LongestNonDecreasingSubseq (str : List Char) : Nat :=
  if str.length = 0 then 0
  else if str.length = 1 then 1
  else LongestNonDecreasingSubseqHelper str 1 1 1

def CountZeros (str : List Char) : Nat :=
  str.filter (· = '0') |>.length

def SameSubsequenceLengths (s t : List Char) : Prop :=
  ∀ l r, 0 ≤ l ∧ l ≤ r ∧ r ≤ s.length →
    LongestNonDecreasingSubseq (s.drop l |>.take (r - l)) = 
    LongestNonDecreasingSubseq (t.drop l |>.take (r - l))

def ValidSolution (s t : List Char) : Prop :=
  s.length = t.length ∧ SameSubsequenceLengths s t

@[reducible, simp]
def solve_precond (s : List Char) : Prop :=
  s.length > 0 ∧ ValidBinaryString s
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Lemmas about ValidBinaryString preservation
lemma ValidBinaryString_same (s : List Char) (h : ValidBinaryString s) : ValidBinaryString s := h

-- LLM HELPER: Reflexivity of SameSubsequenceLengths
lemma SameSubsequenceLengths_refl (s : List Char) : SameSubsequenceLengths s s := by
  intro l r h_bounds
  rfl

-- LLM HELPER: Reflexivity of ValidSolution
lemma ValidSolution_refl (s : List Char) : ValidSolution s s := by
  constructor
  · rfl
  · exact SameSubsequenceLengths_refl s
-- </vc-helpers>

-- <vc-definitions>
def solve (s : List Char) (h_precond : solve_precond s) : List Char :=
  -- Return the same string since it trivially satisfies all requirements
  s
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : List Char) (result : List Char) (h_precond : solve_precond s) : Prop :=
  ValidBinaryString result ∧ ValidSolution s result

theorem solve_spec_satisfied (s : List Char) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  unfold solve_postcond ValidSolution
  constructor
  · -- ValidBinaryString result
    exact h_precond.2
  · -- ValidSolution s result  
    constructor
    · -- s.length = result.length
      rfl
    · -- SameSubsequenceLengths s result
      exact SameSubsequenceLengths_refl s
-- </vc-theorems>
