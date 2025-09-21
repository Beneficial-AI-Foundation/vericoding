-- <vc-preamble>
def split_lines (_ : String) : List String :=
  []

def parse_first_line (_ : String) : (Nat × Nat × Nat × Nat) :=
  (1, 1, 1, 1)

def parse_levels (_ : List String) (_ _ _ : Nat) : List (List String) :=
  []

def int_to_string (_ : Nat) : String :=
  ""

def parse_dependency_line (_ : String) : (Nat × Nat) :=
  (1, 0)

def calculate_mst_cost (_ _ _ _ : Nat) (_ : List (List String)) : Nat :=
  0

def is_valid_spanning_tree (_ : List String) (_ : Nat) : Bool :=
  true

def count_differences (_ _ : List String) (_ _ : Nat) : Nat :=
  0

def ValidInput (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧
  (if stdin_input.length > 0 then 
     stdin_input.data[stdin_input.length - 1]! = '\n' 
   else True) ∧
  let lines := split_lines stdin_input
  lines.length ≥ 1 ∧
  ∃ n m k w : Nat, (
      parse_first_line (lines[0]!) = (n, m, k, w) ∧
      1 ≤ n ∧ n ≤ 10 ∧ 1 ≤ m ∧ m ≤ 10 ∧ 1 ≤ k ∧ k ≤ 1000 ∧ 1 ≤ w ∧ w ≤ 1000 ∧
      lines.length ≥ 1 + k * n ∧
      (∀ i, 1 ≤ i ∧ i < 1 + k * n → (lines[i]!).length = m) ∧
      (∀ i, 1 ≤ i ∧ i < 1 + k * n → 
          ∀ j, 0 ≤ j ∧ j < (lines[i]!).length → 
              let c := (lines[i]!).data[j]!
              (c = '.' ∨ ('a' ≤ c ∧ c ≤ 'z') ∨ ('A' ≤ c ∧ c ≤ 'Z')))
  )

def ValidOutput (result : String) (stdin_input : String) : Prop :=
  result.length > 0 ∧
  (if result.length > 0 then 
     result.data[result.length - 1]! = '\n' 
   else True) ∧
  let result_lines := split_lines result
  let lines := split_lines stdin_input
  lines.length ≥ 1 ∧
  ∃ n m k w : Nat, ∃ input_levels : List (List String), (
      parse_first_line (lines[0]!) = (n, m, k, w) ∧
      1 ≤ n ∧ n ≤ 10 ∧ 1 ≤ m ∧ m ≤ 10 ∧ 1 ≤ k ∧ k ≤ 1000 ∧ 1 ≤ w ∧ w ≤ 1000 ∧
      lines.length ≥ 1 + k * n ∧
      input_levels = parse_levels lines n m k ∧
      input_levels.length = k ∧
      (∀ i, 0 ≤ i ∧ i < k → (input_levels[i]!).length = n) ∧
      (∀ i, 0 ≤ i ∧ i < k → ∀ j, 0 ≤ j ∧ j < n → (input_levels[i]![j]!).length = m) ∧
      result_lines.length = k + 1 ∧
      ∃ total_cost : Nat, (
          result_lines[0]! = int_to_string total_cost ∧
          total_cost = calculate_mst_cost n m k w input_levels ∧
          (∀ i, 1 ≤ i ∧ i ≤ k → 
              ∃ level parent : Nat, (
                  parse_dependency_line (result_lines[i]!) = (level, parent) ∧
                  1 ≤ level ∧ level ≤ k ∧
                  0 ≤ parent ∧ parent ≤ k ∧
                  level ≠ parent
              )) ∧
          (∀ level, 1 ≤ level ∧ level ≤ k → 
              ∃ i, 1 ≤ i ∧ i ≤ k ∧ 
                  (parse_dependency_line (result_lines[i]!)).1 = level ∧
                  (∀ j, 1 ≤ j ∧ j ≤ k ∧ j ≠ i → 
                      (parse_dependency_line (result_lines[j]!)).1 ≠ level)) ∧
          is_valid_spanning_tree result_lines k
      )
  )

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  ValidInput stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (_ : solve_precond stdin_input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (_ : solve_precond stdin_input) : Prop :=
  ValidOutput result stdin_input

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>