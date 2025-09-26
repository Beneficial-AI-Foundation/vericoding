import Mathlib
-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length ≥ 0

def StartsWith_func (s : String) (p : String) : Bool :=
  p.length ≤ s.length ∧ (∀ i : Nat, i < p.length → s.data[i]! = p.data[i]!)

def EndsWith_func (s : String) (suf : String) : Bool :=
  suf.length ≤ s.length ∧ (∀ i : Nat, i < suf.length → s.data[s.length - suf.length + i]! = suf.data[i]!)

def ClassifySentence_func (sentence : String) : String :=
  if EndsWith_func sentence "lala." ∧ ¬StartsWith_func sentence "miao." then "Freda's"
  else if StartsWith_func sentence "miao." ∧ ¬EndsWith_func sentence "lala." then "Rainbow's"
  else "OMG>.< I don't know!"

def ParseInt_helper (s : String) (i : Nat) (acc : Int) : Int :=
  if i ≥ s.length ∨ ¬(s.data[i]! ≥ '0' ∧ s.data[i]! ≤ '9') then acc
  else ParseInt_helper s (i + 1) (acc * 10 + (s.data[i]!.toNat - '0'.toNat))
termination_by s.length - i

def ParseInt_func (s : String) : Int :=
  if s.length = 0 then 0
  else max 0 (ParseInt_helper s 0 0)

def SplitLines_helper (input : String) (i : Nat) (current : String) (acc : List String) : List String :=
  if i ≥ input.length then
    if current.length > 0 then acc ++ [current] else acc
  else if input.data[i]! = '\n' then
    SplitLines_helper input (i + 1) "" (acc ++ [current])
  else
    SplitLines_helper input (i + 1) (current.push input.data[i]!) acc
termination_by input.length - i

def SplitLines_func (input : String) : List String :=
  if input.length = 0 then []
  else SplitLines_helper input 0 "" []

def BuildOutput_func (lines : List String) (n : Nat) : String :=
  if n = 0 then ""
  else if n = 1 ∧ lines.length > 1 then ClassifySentence_func lines[1]!
  else if n > 1 ∧ lines.length > n then BuildOutput_func lines (n - 1) ++ "\n" ++ ClassifySentence_func lines[n]!
  else ""
termination_by n

def mymin (a : Int) (b : Int) : Int :=
  if a ≤ b then a else b

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma BuildOutput_func_length_nonneg (lines : List String) (n : Nat) :
    (BuildOutput_func lines n).length ≥ 0 := by
  omega
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  let lines := SplitLines_func input
  if h : lines.length = 0 then 
    ""
  else
    let n := ParseInt_func lines[0]!
    BuildOutput_func lines (mymin n (lines.length - 1)).natAbs
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result.length ≥ 0 ∧
  (let lines := SplitLines_func input
   if lines.length = 0 then result = ""
   else (let n := ParseInt_func lines[0]!
         result = BuildOutput_func lines (mymin n (lines.length - 1)).natAbs))

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  unfold solve_postcond solve
  simp only [ge_iff_le, tsub_le_iff_right]
  split
  next h => 
    simp [h]
  next h =>
    constructor
    · apply BuildOutput_func_length_nonneg
    · rfl
-- </vc-theorems>
