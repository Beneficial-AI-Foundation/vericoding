import Mathlib
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
-- LLM HELPER
theorem length_pos_of_precond {input : String} (h : solve_precond input) : input.length > 0 := by
  simpa [solve_precond, ValidInput] using h

-- LLM HELPER
theorem CountFaceSquaresAsString_len_pos_of_precond {input : String} (h : solve_precond input) :
  (CountFaceSquaresAsString input).length > 0 := by
  have hlen : input.length > 0 := length_pos_of_precond h
  exact CountFaceSquaresAsString_nonempty input hlen
-- </vc-helpers>

-- <vc-definitions>
noncomputable def solve (input : String) (h_precond : solve_precond input) : String :=
  CountFaceSquaresAsString input
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result.length > 0 ∧ result = CountFaceSquaresAsString input

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  constructor
  · have hlen : input.length > 0 := length_pos_of_precond h_precond
    simpa [solve] using CountFaceSquaresAsString_nonempty input hlen
  · simp [solve]
-- </vc-theorems>
