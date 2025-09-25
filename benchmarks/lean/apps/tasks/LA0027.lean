-- <vc-preamble>
def CountNewlines (s : String) (start : Nat) : Nat :=
  (s.toList.drop start).count '\n'

@[reducible, simp]
def ContainsFourLines (s : String) : Prop :=
  CountNewlines s 0 ≥ 3

@[reducible, simp]
def AllLinesHaveFourValidIntegers (s : String) : Prop :=
  ∀ i : Nat, i < s.length → (s.data[i]! = '0' ∨ s.data[i]! = '1' ∨ s.data[i]! = ' ' ∨ s.data[i]! = '\n')

@[reducible, simp]
def ValidInputString (s : String) : Prop :=
  s.length ≥ 7 ∧
  ContainsFourLines s ∧
  AllLinesHaveFourValidIntegers s

@[reducible, simp]
def StringContainsFourLinesOfFourIntegers (s : String) (input_lines : List (List Int)) : Prop :=
  input_lines.length = 4 ∧
  (∀ i : Nat, i < 4 → input_lines[i]!.length = 4) ∧
  ValidInputString s

@[reducible, simp]
def ParseInput (s : String) (input_lines : List (List Int)) : Prop :=
  input_lines.length = 4 ∧
  (∀ i : Nat, i < 4 → input_lines[i]!.length = 4) ∧
  (∀ i : Nat, i < 4 → ∀ j : Nat, j < 4 → 
      (input_lines[i]![j]! ≥ 0 ∧ input_lines[i]![j]! ≤ 1)) ∧
  StringContainsFourLinesOfFourIntegers s input_lines

@[reducible, simp]
def AccidentAtLane (i : Nat) (lanes : List (List Int)) : Prop :=
  i < 4 ∧
  lanes.length = 4 ∧
  (∀ j : Nat, j < 4 → lanes[j]!.length = 4) ∧
  ((lanes[i]![3]! = 1 ∧ (lanes[i]![0]! = 1 ∨ lanes[i]![1]! = 1 ∨ lanes[i]![2]! = 1)) ∨
  (lanes[i]![0]! = 1 ∧ lanes[(i + 3) % 4]![3]! = 1) ∨
  (lanes[i]![1]! = 1 ∧ lanes[(i + 2) % 4]![3]! = 1) ∨
  (lanes[i]![2]! = 1 ∧ lanes[(i + 1) % 4]![3]! = 1))

@[reducible, simp]
def AccidentPossible (lanes : List (List Int)) : Prop :=
  lanes.length = 4 ∧
  (∀ i : Nat, i < 4 → lanes[i]!.length = 4) ∧
  (∀ i : Nat, i < 4 → ∀ j : Nat, j < 4 → 
      (lanes[i]![j]! = 0 ∨ lanes[i]![j]! = 1)) ∧
  ∃ i : Nat, i < 4 ∧ AccidentAtLane i lanes

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  s.length > 0 ∧
  (∀ i : Nat, i < s.length → (s.data[i]!).val ≥ 0 ∧ (s.data[i]!).val ≤ 127) ∧
  ValidInputString s
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result : String) (h_precond : solve_precond s) : Prop :=
  (result = "YES\n" ∨ result = "NO\n") ∧
  (∃ input_lines, 
      ParseInput s input_lines ∧ 
      (result = "YES\n" ↔ AccidentPossible input_lines)) ∧
  result.length ≥ 3

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  sorry
-- </vc-theorems>