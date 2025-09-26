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
def my_nat_abs (i : Int) : Nat := if i < 0 then (-i).natAbs else i.natAbs

def my_list_drop {α : Type u} (l : List α) (n : Nat) : List α :=
  match n with
  | 0 => l
  | Nat.succ n' => match l with
    | [] => []
    | _ :: t => my_list_drop t n'
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
  rw [solve_postcond, solve]
  simp (config := {decide := true}) [solve_precond, ValidInput]
  exact CountFaceSquaresAsString_nonempty input h_precond
-- </vc-theorems>
