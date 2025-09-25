-- <vc-preamble>
def split_lines (s : String) : List String :=
  []

def parse_first_line_bamboo (line : String) : (Nat × Nat × Nat × Nat) :=
  (0, 0, 0, 0)

def parse_bamboo_length (line : String) : Nat :=
  0

def int_to_string (n : Nat) : String :=
  ""

def string_to_int (s : String) : Nat :=
  0

def AbsDiff (a b : Nat) : Nat :=
  if a ≥ b then a - b else b - a

def CountGroupMembers (assignment : List Nat) (group : Nat) : Nat :=
  match assignment with
  | [] => 0
  | h :: t => (if h = group then 1 else 0) + CountGroupMembers t group

def CalculateGroupSum (input : String) (assignment : List Nat) (group : Nat) : Nat :=
  0

def HasAllThreeGroups (assignment : List Nat) : Prop :=
  (∃ i, i < assignment.length ∧ assignment[i]! = 1) ∧
  (∃ i, i < assignment.length ∧ assignment[i]! = 2) ∧
  (∃ i, i < assignment.length ∧ assignment[i]! = 3)

def CompositionCost (assignment : List Nat) : Nat :=
  let group_a_size := CountGroupMembers assignment 1
  let group_b_size := CountGroupMembers assignment 2
  let group_c_size := CountGroupMembers assignment 3
  (if group_a_size > 0 then (group_a_size - 1) * 10 else 0) +
  (if group_b_size > 0 then (group_b_size - 1) * 10 else 0) +
  (if group_c_size > 0 then (group_c_size - 1) * 10 else 0)

def AdjustmentCost (input : String) (assignment : List Nat) : Nat :=
  let lines := split_lines input
  let (N, A, B, C) := parse_first_line_bamboo lines[0]!
  let sum_a := CalculateGroupSum input assignment 1
  let sum_b := CalculateGroupSum input assignment 2
  let sum_c := CalculateGroupSum input assignment 3
  AbsDiff sum_a A + AbsDiff sum_b B + AbsDiff sum_c C

def CalculateAssignmentCost (input : String) (assignment : List Nat) : Nat :=
  CompositionCost assignment + AdjustmentCost input assignment

def ValidInput (input : String) : Prop :=
  ∃ lines, (lines = split_lines input ∧
  lines.length ≥ 2 ∧
  ∃ N A B C, 
      parse_first_line_bamboo lines[0]! = (N, A, B, C) ∧
      3 ≤ N ∧ N ≤ 8 ∧
      1 ≤ C ∧ C < B ∧ B < A ∧ A ≤ 1000 ∧
      lines.length ≥ N + 1 ∧
      ∀ i, 1 ≤ i ∧ i ≤ N → 
          ∃ li, parse_bamboo_length lines[i]! = li ∧ 1 ≤ li ∧ li ≤ 1000)

def ValidAssignment (input : String) (assignment : List Nat) : Prop :=
  ValidInput input →
  ∃ lines N A B C, 
      lines = split_lines input ∧
      parse_first_line_bamboo lines[0]! = (N, A, B, C) ∧
      assignment.length = N ∧
      (∀ i, i < N → assignment[i]! < 4) ∧
      HasAllThreeGroups assignment

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧
  (stdin_input.get! ⟨stdin_input.length - 1⟩ = '\n' ∨ ∃ i, 0 ≤ i ∧ i < stdin_input.length ∧ stdin_input.get! ⟨i⟩ = '\n') ∧
  ValidInput (stdin_input ++ (if stdin_input.get! ⟨stdin_input.length - 1⟩ = '\n' then "" else "\n"))
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (h_precond : solve_precond stdin_input) : Prop :=
  result.length > 0 ∧
  result.get! ⟨result.length - 1⟩ = '\n' ∧
  (∃ val, val ≥ 0 ∧ result = int_to_string val ++ "\n") ∧
  (∀ assignment, ValidAssignment (stdin_input ++ (if stdin_input.get! ⟨stdin_input.length - 1⟩ = '\n' then "" else "\n")) assignment →
      string_to_int (result.take (result.length - 1)) ≤ CalculateAssignmentCost (stdin_input ++ (if stdin_input.get! ⟨stdin_input.length - 1⟩ = '\n' then "" else "\n")) assignment)

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>