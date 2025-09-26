import Mathlib
-- <vc-preamble>
def ValidInput (input : List String) : Prop :=
  input.length = 8 ∧
  (∀ i, 0 ≤ i ∧ i < 8 → (input.get! i).length = 8) ∧
  (∀ i j, 0 ≤ i ∧ i < 8 ∧ 0 ≤ j ∧ j < 8 → (input.get! i).data.get! j = 'W' ∨ (input.get! i).data.get! j = 'B')

def HasAlternatingRow (row : String) : Prop :=
  row.length = 8 ∧
  (∀ j, 0 ≤ j ∧ j < 8 → row.data.get! j = 'W' ∨ row.data.get! j = 'B') ∧
  (∀ k, 1 ≤ k ∧ k < 8 → row.data.get! k ≠ row.data.get! (k-1))

def AllRowsHaveAlternatingPattern (input : List String) : Prop :=
  ValidInput input ∧
  (∀ i, 0 ≤ i ∧ i < 8 → HasAlternatingRow (input.get! i))

@[reducible, simp]
def solve_precond (input : List String) : Prop :=
  ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/--
Checks if a single row has alternating 'W' and 'B' characters.
This is a computable version of the alternating condition in `HasAlternatingRow`.
It uses `List.zipWith` to compare adjacent characters.
-/
def checkRow (row : String) : Bool :=
  let chars := row.data
  (List.zipWith (fun c1 c2 => c1 != c2) chars (chars.drop 1)).all id

-- LLM HELPER
/--
Checks if all rows in the input have an alternating pattern.
-/
def checkAllRows (input : List String) : Bool :=
  input.all checkRow
-- </vc-helpers>

-- <vc-definitions>
def solve (input : List String) (h_precond : solve_precond input) : String :=
  if checkAllRows input then "YES" else "NO"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : List String) (result : String) (h_precond : solve_precond input) : Prop :=
  result = "YES" ∨ result = "NO"

theorem solve_spec_satisfied (input : List String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  dsimp [solve]
  split_ifs <;> simp
-- </vc-theorems>
