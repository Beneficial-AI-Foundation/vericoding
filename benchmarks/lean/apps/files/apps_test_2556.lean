-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length > 0

noncomputable axiom SplitLines : String → List String
axiom ParseInt : String → Int
axiom GetPairsFromLines : List String → Int → Int → List (Int × Int)
noncomputable axiom FormatResultsHelper : List Int → Int → String → String

def ComputeMinimumCost (c : Int) (s : Int) : Int :=
  let a := s / c
  let r := s % c
  (c - r) * a * a + r * (a + 1) * (a + 1)

noncomputable def GetInputPairs (input : String) : List (Int × Int) :=
  let lines := SplitLines input
  if lines.isEmpty then []
  else 
    let n := ParseInt lines[0]!
    GetPairsFromLines lines 1 n

noncomputable def FormatResults (results : List Int) : String :=
  FormatResultsHelper results 0 ""

noncomputable def ValidOutput (input : String) (output : String) : Prop :=
  let inputPairs := GetInputPairs input
  let expectedResults := inputPairs.map (fun pair => 
    if pair.1 > 0 ∧ pair.2 ≥ 0 then
      ComputeMinimumCost pair.1 pair.2
    else 0)
  output = FormatResults expectedResults

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
noncomputable def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
noncomputable def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  ValidOutput input result

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>