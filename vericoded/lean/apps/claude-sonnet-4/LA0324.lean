import Mathlib
-- <vc-preamble>
def ValidBinaryString (s : String) : Prop :=
  ∀ i, 0 ≤ i ∧ i < s.length → s.data[i]! = '0' ∨ s.data[i]! = '1'

def countZeros (s : String) : Int :=
  s.data.foldl (fun acc c => if c = '0' then acc + 1 else acc) 0

def countOnes (s : String) : Int :=
  s.data.foldl (fun acc c => if c = '1' then acc + 1 else acc) 0

def longestNonDecreasingSubseqLengthComplete (s : String) : Int :=
  if s.length = 0 then 0
  else if s.length = 1 then 1
  else 
    let countOnes := countOnes s
    let countZeros := s.length - countOnes
    if countZeros = 0 then countOnes
    else if countOnes = 0 then 1
    else countZeros + countOnes

def longestNonDecreasingSubseqLength (s : String) (l r : Int) : Int :=
  let sub := String.mk (s.data.drop l.natAbs |>.take (r - l + 1).natAbs)
  longestNonDecreasingSubseqLengthComplete sub

def BasicValidSolution (s t : String) : Prop :=
  s.length = t.length ∧
  ValidBinaryString s ∧
  ValidBinaryString t ∧
  (∀ i, 0 ≤ i ∧ i < s.length → s.data[i]! = '0' → t.data[i]! = '0') ∧
  (∀ i, 0 ≤ i ∧ i < s.length → t.data[i]! = '1' → s.data[i]! = '1')

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  ValidBinaryString s
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Basic lemmas for string equality
lemma same_string_same_length (s : String) : s.length = s.length := rfl

lemma valid_string_preserved (s : String) (h : ValidBinaryString s) : ValidBinaryString s := h
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : String :=
  s
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result : String) (h_precond : solve_precond s) : Prop :=
  BasicValidSolution s result

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  unfold solve_postcond BasicValidSolution solve
  constructor
  · rfl
  constructor
  · exact h_precond
  constructor
  · exact h_precond
  constructor
  · intros i hi h_zero
    exact h_zero
  · intros i hi h_one
    exact h_one
-- </vc-theorems>
