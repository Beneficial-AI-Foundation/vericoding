-- <vc-preamble>
structure TestCase where
  n : Nat
  x : Nat
  y : Nat
  z : Nat
  castles : List Nat

def split_by_newline (s : String) : List String := sorry

def is_non_negative_integer_string (s : String) : Bool := sorry

def parse_integer (s : String) : Int := sorry

def is_valid_test_case_params (s : String) : Bool := sorry

def is_valid_castles_line (s : String) (n : Nat) : Bool := sorry

def get_n_from_params (s : String) : Nat := sorry

def get_x_from_params (s : String) : Nat := sorry

def get_y_from_params (s : String) : Nat := sorry

def get_z_from_params (s : String) : Nat := sorry

def count_lines (s : String) : Nat := sorry

def get_line (s : String) (i : Nat) : String := sorry

def parse_castle_array (s : String) : List Nat := sorry

def get_test_count (s : String) : Nat :=
  Int.natAbs (parse_integer ((split_by_newline s)[0]!))

def ValidInput (input : String) : Prop :=
  input.length > 0 ∧
  let lines := split_by_newline input
  lines.length ≥ 1 ∧
  is_non_negative_integer_string (lines[0]!) ∧
  let t := Int.natAbs (parse_integer (lines[0]!))
  1 ≤ t ∧ t ≤ 1000 ∧
  lines.length = 1 + 2 * t ∧
  ∀ i, 0 ≤ i ∧ i < t →
    let params_line := lines[1 + 2*i]!
    let castles_line := lines[2 + 2*i]!
    is_valid_test_case_params params_line ∧
    is_valid_castles_line castles_line (get_n_from_params params_line) ∧
    get_n_from_params params_line ≤ 300000 ∧
    1 ≤ get_x_from_params params_line ∧ get_x_from_params params_line ≤ 5 ∧
    1 ≤ get_y_from_params params_line ∧ get_y_from_params params_line ≤ 5 ∧
    1 ≤ get_z_from_params params_line ∧ get_z_from_params params_line ≤ 5

def ValidOutput (input : String) (output : String) : Prop :=
  output.length > 0 ∧
  output.data[output.length - 1]! = '\n' ∧
  count_lines output = get_test_count input ∧
  ∀ i, 0 ≤ i ∧ i < count_lines output →
    let line := get_line output i
    line ≠ "" → is_non_negative_integer_string line

def get_test_case (s : String) (i : Nat) : TestCase :=
  let lines := split_by_newline s
  let params_line := lines[1 + 2*i]!
  let castles_line := lines[2 + 2*i]!
  ⟨get_n_from_params params_line,
   get_x_from_params params_line,
   get_y_from_params params_line,
   get_z_from_params params_line,
   parse_castle_array castles_line⟩

def count_winning_first_moves (tc : TestCase) : Nat := 0

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  ValidInput stdin_input
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
  ValidOutput stdin_input result ∧
  ∀ i, 0 ≤ i ∧ i < get_test_count stdin_input →
    let output_val := Int.natAbs (parse_integer (get_line result i))
    let test_case := get_test_case stdin_input i
    output_val = count_winning_first_moves test_case

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>
