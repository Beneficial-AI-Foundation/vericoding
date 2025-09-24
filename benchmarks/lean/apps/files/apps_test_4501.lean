-- <vc-preamble>
def split_lines_func (s : String) : List String := s.splitOn "\n"

def split_spaces_func (s : String) : List String := s.splitOn " "

def is_valid_integer (s : String) : Bool := 
  match s.toInt? with
  | some _ => true
  | none => false

def string_to_int_func (s : String) : Int := 
  match s.toInt? with
  | some n => n
  | none => 0

def valid_input_format (stdin_input : String) : Prop :=
  let lines := split_lines_func stdin_input
  lines.length ≥ 2 ∧
  let first_line := split_spaces_func (lines[0]!)
  let second_line := split_spaces_func (lines[1]!)
  first_line.length = 2 ∧
  is_valid_integer (first_line[0]!) ∧
  is_valid_integer (first_line[1]!) ∧
  let N := string_to_int_func (first_line[0]!)
  let A := string_to_int_func (first_line[1]!)
  1 ≤ N ∧ N ≤ 50 ∧
  1 ≤ A ∧ A ≤ 50 ∧
  second_line.length = N.natAbs ∧
  (∀ j, 0 ≤ j ∧ j < second_line.length →
      is_valid_integer (second_line[j]!) ∧
      1 ≤ string_to_int_func (second_line[j]!) ∧ string_to_int_func (second_line[j]!) ≤ 50)

def is_valid_output (output : String) : Prop :=
  output.length > 1 ∧
  output.back = '\n' ∧
  let result_str := output.dropRight 1
  is_valid_integer result_str ∧
  string_to_int_func result_str ≥ 0

def count_subsets_with_sum (differences : List Int) (target : Int) : Nat :=
  match differences with
  | [] => if target = 0 then 1 else 0
  | d :: ds => count_subsets_with_sum ds target + count_subsets_with_sum ds (target - d)

def count_zero_sum_subsets (differences : List Int) : Nat :=
  match differences with
  | [] => 1
  | d :: ds => 
      let rest_count := count_zero_sum_subsets ds
      rest_count + count_subsets_with_sum ds (-d)

def count_valid_selections (cards : List Int) (A : Int) : Int :=
  let differences := cards.map (fun x => x - A)
  let total := count_zero_sum_subsets differences
  if total > 0 then Int.ofNat total - 1 else 0

def output_represents_correct_count (stdin_input : String) (output : String) : Prop :=
  let lines := split_lines_func stdin_input
  let first_line := split_spaces_func (lines[0]!)
  let second_line := split_spaces_func (lines[1]!)
  let N := string_to_int_func (first_line[0]!)
  let A := string_to_int_func (first_line[1]!)
  let cards := (List.range N.natAbs).map (fun i => string_to_int_func (second_line[i]!))
  let result := string_to_int_func (output.dropRight 1)
  result = count_valid_selections cards A

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧ valid_input_format stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (output : String) (h_precond : solve_precond stdin_input) : Prop :=
  output.length > 0 ∧
  output.back = '\n' ∧
  is_valid_output output ∧
  output_represents_correct_count stdin_input output

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>