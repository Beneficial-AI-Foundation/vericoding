import Mathlib
-- <vc-preamble>

def set_from_seq (s : List Int) : List Int :=
  s.eraseDups

def split_lines (s : String) : List String :=
  s.splitOn "\n" |>.map (fun line => if line.endsWith "\r" then line.dropRight 1 else line)

def find_char (s : String) (c : Char) : Int :=
  let chars := s.toList
  match chars.findIdx? (· = c) with
  | some idx => idx
  | none => -1

def is_valid_digits (s : String) : Bool :=
  s.toList.all (fun c => '0' ≤ c ∧ c ≤ '9')

def char_to_digit (c : Char) : Int :=
  (c.val.toNat - '0'.val.toNat : Int)

def parse_int_helper (s : String) : Int :=
  s.toList.foldl (fun acc c => acc * 10 + char_to_digit c) 0

def parse_int (s : String) : Int :=
  if s.isEmpty then 0
  else if s.get! 0 = '-' then
    if is_valid_digits (s.drop 1) then -(parse_int_helper (s.drop 1)) else 0
  else if is_valid_digits s then parse_int_helper s else 0

def parse_int_list (s : String) : List Int :=
  s.splitOn " " |>.map parse_int

def ValidInput (stdin_input : String) : Prop :=
  let lines := split_lines stdin_input
  lines.length ≥ 3 ∧
  let n := parse_int (lines[0]!)
  let x_line := parse_int_list (lines[1]!)
  let y_line := parse_int_list (lines[2]!)
  n ≥ 1 ∧ x_line.length > 0 ∧ y_line.length > 0 ∧
  (x_line[0]!) ≥ 0 ∧ (y_line[0]!) ≥ 0 ∧
  x_line.length ≥ 1 + (x_line[0]!).natAbs ∧ y_line.length ≥ 1 + (y_line[0]!).natAbs

def GetExpectedOutput (stdin_input : String) : String :=
  let lines := split_lines stdin_input
  let n := parse_int (lines[0]!)
  let x_line := parse_int_list (lines[1]!)
  let y_line := parse_int_list (lines[2]!)
  let x_count := x_line[0]!
  let y_count := y_line[0]!
  let x_levels := set_from_seq (x_line.drop 1 |>.take x_count.natAbs)
  let y_levels := set_from_seq (y_line.drop 1 |>.take y_count.natAbs)
  let all_levels := (x_levels ++ y_levels).eraseDups
  let required_levels := (List.range n.natAbs).map (fun (i : Nat) => (i : Int) + 1)
  if required_levels.all (fun i => all_levels.contains i) then "I become the guy." else "Oh, my keyboard!"

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  ValidInput stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem GetExpectedOutput_id (s : String) : GetExpectedOutput s = GetExpectedOutput s := rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  GetExpectedOutput stdin_input
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (h_precond : solve_precond stdin_input) : Prop :=
  result = GetExpectedOutput stdin_input

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  rfl
-- </vc-theorems>
