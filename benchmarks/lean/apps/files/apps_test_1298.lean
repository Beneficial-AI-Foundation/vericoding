-- <vc-preamble>
def is_binary_string (s : String) : Prop :=
  ∀ i, i < s.length → s.data[i]! = '0' ∨ s.data[i]! = '1'

def is_valid_integer (s : String) : Prop :=
  s.length > 0 ∧ (s.data[0]! ≠ '0' ∨ s.length = 1) ∧ 
  ∀ i, i < s.length → '0' ≤ s.data[i]! ∧ s.data[i]! ≤ '9'

def count_char : String → Char → Nat
  | ⟨[]⟩, _ => 0
  | ⟨c :: cs⟩, target => (if c = target then 1 else 0) + count_char ⟨cs⟩ target

def abs_diff_count (s : String) : Nat :=
  let count0 := count_char s '0'
  let count1 := count_char s '1'
  if count1 ≥ count0 then count1 - count0 else count0 - count1

def char_of_digit (d : Nat) : Char :=
  match d with
  | 0 => '0'
  | 1 => '1'
  | 2 => '2'
  | 3 => '3'
  | 4 => '4'
  | 5 => '5'
  | 6 => '6'
  | 7 => '7'
  | 8 => '8'
  | 9 => '9'
  | _ => '0'

def int_to_string : Nat → String
  | 0 => "0"
  | n => if n < 10 then String.mk [char_of_digit n]
         else int_to_string (n / 10) ++ String.mk [char_of_digit (n % 10)]

def string_to_int (s : String) : Nat :=
  s.toList.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def substring_helper (s : String) (start_pos end_pos : Nat) : String :=
  String.mk (s.toList.drop start_pos |>.take (end_pos - start_pos))

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧
  (∃ i, i < stdin_input.length ∧ stdin_input.data[i]! = '\n') ∧
  (∃ newline_pos, newline_pos < stdin_input.length ∧ 
   stdin_input.data[newline_pos]! = '\n' ∧
   newline_pos + 1 < stdin_input.length ∧
   (∃ binary_end, newline_pos + 1 ≤ binary_end ∧ binary_end ≤ stdin_input.length ∧
    (binary_end = stdin_input.length ∨ (binary_end < stdin_input.length ∧ stdin_input.data[binary_end]! = '\n')) ∧
    is_valid_integer (substring_helper stdin_input 0 newline_pos) ∧
    is_binary_string (substring_helper stdin_input (newline_pos + 1) binary_end)))
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
  result.data[result.length - 1]! = '\n' ∧
  (∃ newline_pos, newline_pos < stdin_input.length ∧ 
   stdin_input.data[newline_pos]! = '\n' ∧
   newline_pos + 1 < stdin_input.length ∧
   (∃ binary_end, newline_pos + 1 ≤ binary_end ∧ binary_end ≤ stdin_input.length ∧
    (binary_end = stdin_input.length ∨ (binary_end < stdin_input.length ∧ stdin_input.data[binary_end]! = '\n')) ∧
    is_binary_string (substring_helper stdin_input (newline_pos + 1) binary_end) ∧
    result = int_to_string (abs_diff_count (substring_helper stdin_input (newline_pos + 1) binary_end)) ++ "\n"))

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>