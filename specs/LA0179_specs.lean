-- <vc-preamble>
def ParseInputLines (input : String) : List String :=
  input.splitOn "\n"

def FindNextNewline (input : String) (start : Nat) : Int :=
  let rec findHelper (pos : Nat) : Int :=
    if pos ≥ input.length then -1
    else if input.data[pos]! = '\n' then pos
    else findHelper (pos + 1)
  findHelper start

def CountBlackInSquare (lines : List String) (row col : Nat) : Int :=
  let getChar (r c : Nat) : Char :=
    match lines[r]? with
    | none => '.'
    | some s => if c < s.length then s.data[c]! else '.'
  let cell1 := if getChar row col = '#' then 1 else 0
  let cell2 := if getChar row (col + 1) = '#' then 1 else 0
  let cell3 := if getChar (row + 1) col = '#' then 1 else 0
  let cell4 := if getChar (row + 1) (col + 1) = '#' then 1 else 0
  cell1 + cell2 + cell3 + cell4

def ValidGrid (lines : List String) : Prop :=
  lines.length = 4 ∧ (∀ k, k < 4 → match lines[k]? with | none => False | some s => s.length ≥ 4)

def CanMakeUniformSquare (lines : List String) : Prop :=
  ValidGrid lines →
  ∃ i j, i ≤ 2 ∧ j ≤ 2 ∧ 
    i + 1 < lines.length ∧ 
    (match lines[i]? with | none => False | some s => j + 1 < s.length) ∧
    (match lines[i + 1]? with | none => False | some s => j + 1 < s.length) ∧
    (let blackCount := CountBlackInSquare lines i j
     blackCount ≥ 3 ∨ blackCount ≤ 1)

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
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  (result = "YES" ∨ result = "NO") ∧
  (result = "YES" ↔ 
    (let lines := ParseInputLines input
     ValidGrid lines ∧ CanMakeUniformSquare lines))

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>