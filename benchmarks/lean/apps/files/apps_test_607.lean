-- <vc-preamble>
def SplitLinesFunc (input : String) : List String := 
  input.splitOn "\n"

def SplitSpacesFunc (line : String) : List String := 
  line.splitOn " "

def StringToInt (s : String) : Int := 
  s.toInt?.getD 0

def IntToString (n : Int) : String := 
  toString n

def SumUpToSize (_ _ _ : Int) : Int := 
  0

def ParseTwoInts (input : String) : Int × Int :=
  if input.length > 0 then
    let lines := SplitLinesFunc input
    if lines.length = 0 then (0, 0)
    else
      let parts := SplitSpacesFunc lines[0]!
      if parts.length < 2 then (0, 0)
      else (StringToInt parts[0]!, StringToInt parts[1]!)
  else (0, 0)

@[reducible, simp]
def ValidInput (input : String) : Prop :=
  input.length > 0 ∧
  (let nm := ParseTwoInts input
   let n := nm.fst
   let m := nm.snd
   n > 0 ∧ m > 0)

def ComputeHappinessSum (n : Int) (m : Int) : Int :=
  if n > 0 ∧ m > 0 then SumUpToSize n m n else 0

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (output : String) (h_precond : solve_precond input) : Prop :=
  output.length ≥ 0 ∧
  (ValidInput input →
    (let nm := ParseTwoInts input
     let n := nm.fst
     let m := nm.snd
     output = IntToString (ComputeHappinessSum n m) ++ "\n")) ∧
  (ValidInput input → output.length > 0 ∧ output.data[output.length - 1]! = '\n') ∧
  (ValidInput input → ∀ c, c ∈ output.data → (c = '\n' ∨ ('0' ≤ c ∧ c ≤ '9'))) ∧
  (¬ValidInput input → output = "")

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>