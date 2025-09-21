-- <vc-preamble>
def valid_input_format (s : String) : Prop :=
  s.length ≥ 7 ∧ ∃ pos, 0 < pos ∧ pos < s.length ∧ s.data.get! pos = '\n'

def get_test_count (stdin_input : String) : Int := 1

def get_array_sum (stdin_input : String) (test_idx : Int) : Int := 0

def get_target_m (stdin_input : String) (test_idx : Int) : Int := 0

def compute_expected_output (stdin_input : String) (start : Int) (count : Int) : String := ""

def expected_output_for_input (stdin_input : String) : String :=
  compute_expected_output stdin_input 0 (get_test_count stdin_input)

def count_responses (result : String) : Int := 0

def get_response_at_index (result : String) (i : Int) : String := ""

def behavioral_correctness (stdin_input : String) (result : String) : Prop :=
  let T := get_test_count stdin_input
  count_responses result = T ∧
  (∀ i, 0 ≤ i ∧ i < T →
    let array_sum := get_array_sum stdin_input i
    let target_m := get_target_m stdin_input i
    let response := get_response_at_index result i
    (array_sum = target_m ↔ response = "YES\n") ∧
    (array_sum ≠ target_m ↔ response = "NO\n"))

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  valid_input_format stdin_input ∧
  stdin_input.length > 0 ∧
  stdin_input ≠ "" ∧
  '\n' ∈ stdin_input.data ∧
  ∃ pos, 0 ≤ pos ∧ pos < stdin_input.length ∧ stdin_input.data.get! pos = '\n'
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
  behavioral_correctness stdin_input result

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>