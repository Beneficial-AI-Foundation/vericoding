-- <vc-preamble>
def ValidInput (lines : List String) : Prop :=
  lines.length = 3 ∧ ∀ i, 0 ≤ i ∧ i < 3 → (lines[i]!).length = 3

def ExtractDiagonal (lines : List String) : String :=
  String.mk [lines[0]!.data[0]!, lines[1]!.data[1]!, lines[2]!.data[2]!]

@[reducible, simp]
def solve_precond (lines : List String) : Prop :=
  ValidInput lines
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (lines : List String) (h_precond : solve_precond lines) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (lines : List String) (result : String) (h_precond : solve_precond lines) : Prop :=
  result.length = 4 ∧
  result.data[0]! = lines[0]!.data[0]! ∧
  result.data[1]! = lines[1]!.data[1]! ∧
  result.data[2]! = lines[2]!.data[2]! ∧
  result.data[3]! = '\n' ∧
  result = ExtractDiagonal lines ++ "\n"

theorem solve_spec_satisfied (lines : List String) (h_precond : solve_precond lines) :
    solve_postcond lines (solve lines h_precond) h_precond := by
  sorry
-- </vc-theorems>