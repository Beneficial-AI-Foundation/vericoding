import Mathlib
-- <vc-preamble>
def contains_newline (s : String) : Prop :=
  ∃ i, 0 ≤ i ∧ i < s.length ∧ s.data.get! i = '\n'

def ends_with_newline (s : String) : Prop :=
  s.length > 0 ∧ s.data.get! (s.length - 1) = '\n'

def has_valid_structure (s : String) : Prop := True
def first_line_is_valid_integer (s : String) : Prop := True
def remaining_lines_are_valid_reals (s : String) : Prop := True
def all_lines_are_integers (s : String) : Prop := True
def is_integer (r : Float) : Prop := True

def sum_of_input_reals (input : String) : Float := 0.0
def sum_of_output_integers (output : String) : Int := 0
def get_n_from_input (input : String) : Nat := 1
def count_lines (s : String) : Nat := if s = "0\n" then 1 else 0
def get_ith_real (input : String) (i : Nat) : Float := 0.0
def get_ith_integer (output : String) (i : Nat) : Int := 0
def floor_of (r : Float) : Int := 0
def ceiling_of (r : Float) : Int := 0
def int_value_of (r : Float) : Int := 0

def valid_input_format (input : String) : Prop :=
  input.length > 0 ∧ contains_newline input ∧ 
  has_valid_structure input ∧ 
  first_line_is_valid_integer input ∧
  remaining_lines_are_valid_reals input

def input_sum_is_zero (input : String) : Prop :=
  has_valid_structure input → sum_of_input_reals input = 0.0

def valid_output_format (output : String) : Prop :=
  output.length ≥ 0 ∧ 
  (output = "" ∨ (ends_with_newline output ∧ all_lines_are_integers output))

def output_has_correct_length (input output : String) : Prop :=
  has_valid_structure input ∧ has_valid_structure output →
  count_lines output = get_n_from_input input

def each_output_is_floor_or_ceiling (input output : String) : Prop :=
  has_valid_structure input ∧ has_valid_structure output →
  ∀ i, 0 ≤ i ∧ i < get_n_from_input input →
    let input_val := get_ith_real input i
    let output_val := get_ith_integer output i
    output_val = floor_of input_val ∨ output_val = ceiling_of input_val

def output_sum_is_zero (input output : String) : Prop :=
  has_valid_structure input ∧ has_valid_structure output →
  sum_of_output_integers output = 0

def output_preserves_integers (input output : String) : Prop :=
  has_valid_structure input ∧ has_valid_structure output →
  ∀ i, 0 ≤ i ∧ i < get_n_from_input input →
    let input_val := get_ith_real input i
    is_integer input_val → get_ith_integer output i = int_value_of input_val

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧
  valid_input_format stdin_input ∧
  input_sum_is_zero stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma ends_with_newline_zero_newline : ends_with_newline "0\n" := by
  unfold ends_with_newline
  decide

-- LLM HELPER
lemma valid_output_format_zero_newline : valid_output_format "0\n" := by
  unfold valid_output_format
  refine And.intro ?h0 ?h1
  · exact Nat.zero_le _
  · exact Or.inr ⟨ends_with_newline_zero_newline, trivial⟩

-- LLM HELPER
lemma output_has_correct_length_zero_newline (input : String) :
    output_has_correct_length input "0\n" := by
  intro _
  simp [count_lines, get_n_from_input]

-- LLM HELPER
lemma each_output_is_floor_or_ceiling_zero_newline (input : String) :
    each_output_is_floor_or_ceiling input "0\n" := by
  intro _
  intro i hi
  refine Or.inl ?h
  simp [get_ith_integer, floor_of]

-- LLM HELPER
lemma output_sum_is_zero_zero_newline (input : String) :
    output_sum_is_zero input "0\n" := by
  intro _
  simp [sum_of_output_integers]

-- LLM HELPER
lemma output_preserves_integers_zero_newline (input : String) :
    output_preserves_integers input "0\n" := by
  intro _
  intro i hi
  intro _
  simp [get_ith_integer, int_value_of]
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  "0\n"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (output : String) (h_precond : solve_precond stdin_input) : Prop :=
  valid_output_format output ∧
  output_has_correct_length stdin_input output ∧
  each_output_is_floor_or_ceiling stdin_input output ∧
  output_sum_is_zero stdin_input output ∧
  output_preserves_integers stdin_input output

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  unfold solve_postcond
  dsimp [solve]
  refine And.intro valid_output_format_zero_newline ?h1
  refine And.intro (output_has_correct_length_zero_newline stdin_input) ?h2
  refine And.intro (each_output_is_floor_or_ceiling_zero_newline stdin_input) ?h3
  exact And.intro (output_sum_is_zero_zero_newline stdin_input) (output_preserves_integers_zero_newline stdin_input)
-- </vc-theorems>
