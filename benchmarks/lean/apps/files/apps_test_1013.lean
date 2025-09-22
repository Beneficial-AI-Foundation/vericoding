-- <vc-preamble>

-- Helper functions (axiomatized for now)
axiom SplitLinesFunc : String → List String
axiom SplitWhitespaceFunc : String → List String
axiom StringToIntFunc : String → Int

noncomputable def GetGridCellHelper (lines: List String) (i: Int) (j: Int): String :=
  if lines.length ≥ 2 ∧ i ≥ 0 ∧ j ≥ 0 ∧ i + 1 < lines.length then
    let line := lines[i.natAbs + 1]!
    let parts := SplitWhitespaceFunc line
    if j.natAbs < parts.length then parts[j.natAbs]! else "0"
  else "0"

noncomputable def ValidInput (input: String) : Prop :=
  let lines := SplitLinesFunc input
  lines.length ≥ 2 ∧
  let firstLine := lines[0]!
  let nmParts := SplitWhitespaceFunc firstLine
  nmParts.length ≥ 2 ∧
  let n := StringToIntFunc (nmParts[0]!)
  let m := StringToIntFunc (nmParts[1]!)
  n ≥ 3 ∧ m ≥ 3 ∧
  lines.length ≥ n + 1 ∧
  (∀ i, 1 ≤ i ∧ i ≤ n → 
      let rowParts := SplitWhitespaceFunc (lines[i.natAbs]!)
      rowParts.length ≥ m ∧
      (∀ j, 0 ≤ j ∧ j < m → (rowParts[j.natAbs]!) = "0" ∨ (rowParts[j.natAbs]!) = "1")) ∧
  (∃ i j, 0 ≤ i ∧ i < n ∧ 0 ≤ j ∧ j < m ∧ GetGridCellHelper lines i j = "1") ∧
  GetGridCellHelper lines 0 0 = "0" ∧
  GetGridCellHelper lines 0 (m-1) = "0" ∧
  GetGridCellHelper lines (n-1) 0 = "0" ∧
  GetGridCellHelper lines (n-1) (m-1) = "0"

noncomputable def GetN (input: String) : Int :=
  let lines := SplitLinesFunc input
  let firstLine := lines[0]!
  let parts := SplitWhitespaceFunc firstLine
  StringToIntFunc (parts[0]!)

noncomputable def GetM (input: String) : Int :=
  let lines := SplitLinesFunc input
  let firstLine := lines[0]!
  let parts := SplitWhitespaceFunc firstLine
  StringToIntFunc (parts[1]!)

noncomputable def GetGridCell (input: String) (i: Int) (j: Int): String :=
  let lines := SplitLinesFunc input
  let line := lines[i.natAbs + 1]!
  let parts := SplitWhitespaceFunc line
  parts[j.natAbs]!

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0 ∧ ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result: String) (h_precond : solve_precond input) : Prop :=
  (result = "2\n" ∨ result = "4\n") ∧
  (result = "2\n" ↔ (∃ i j, 0 ≤ i ∧ i < GetN input ∧ 0 ≤ j ∧ j < GetM input ∧ 
                   GetGridCell input i j = "1" ∧ 
                   (i = 0 ∨ j = 0 ∨ i = GetN input - 1 ∨ j = GetM input - 1)))

theorem solve_spec_satisfied (input: String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>