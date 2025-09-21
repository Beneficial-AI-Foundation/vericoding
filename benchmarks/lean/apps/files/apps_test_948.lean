-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length > 0

def ValidGrid (grid : List String) (n m : Int) : Prop :=
  n ≥ 1 ∧ m ≥ 1 ∧ grid.length = n ∧
  ∀ i, 0 ≤ i ∧ i < grid.length → (grid[i]!).length = m

noncomputable axiom SplitLinesFunc : String → List String

noncomputable axiom SplitSpacesFunc : String → List String

noncomputable axiom StringToIntFunc : String → Int

noncomputable axiom IntToStringFunc : Int → String

noncomputable axiom CountValidSquares : List String → Int → Int → Int

noncomputable def CountFaceSquares (input : String) : Int :=
  if h : input.length > 0 then
    let lines := SplitLinesFunc input
    if lines.length = 0 then 0
    else
      let firstLine := lines[0]!
      let nm := SplitSpacesFunc firstLine
      if nm.length < 2 then 0
      else
        let n := StringToIntFunc (nm[0]!)
        let m := StringToIntFunc (nm[1]!)
        if n < 1 ∨ m < 1 ∨ lines.length < (n + 1).natAbs then 0
        else
          let grid := lines.drop 1 |>.take n.natAbs
          CountValidSquares grid n m
  else 0

axiom CountFaceSquares_nonneg (input : String) (h : input.length > 0) : CountFaceSquares input ≥ 0

noncomputable def CountFaceSquaresAsString (input : String) : String :=
  if h : input.length > 0 then
    let count := CountFaceSquares input
    IntToStringFunc count ++ "\n"
  else "\n"

axiom CountFaceSquaresAsString_nonempty (input : String) (h : input.length > 0) : (CountFaceSquaresAsString input).length > 0

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
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result.length > 0 ∧ result = CountFaceSquaresAsString input

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>