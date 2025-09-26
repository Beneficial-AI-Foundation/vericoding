import Mathlib
-- <vc-preamble>
def find_newline (input : String) (start : Nat) : Int :=
  if start ≥ input.length then -1
  else if input.data[start]? = some '\n' then start
  else find_newline input (start + 1)
termination_by input.length - start

def split_lines (input : String) : List String :=
  let newline_pos := find_newline input 0
  if newline_pos = -1 then [input]
  else if newline_pos ≥ 0 ∧ newline_pos < input.length then
    let pos_nat := Int.natAbs newline_pos
    if pos_nat + 1 ≥ input.length then [input.take pos_nat, ""]
    else [input.take pos_nat, input.drop (pos_nat + 1)]
  else [input]

def is_valid_number (s : String) : Bool :=
  s.length > 0 ∧ s.all (fun c => '0' ≤ c ∧ c ≤ '9')

partial def string_to_nat (s : String) : Nat :=
  if s.length = 0 then 0
  else if s.length = 1 then 
    match s.data[0]? with
    | none => 0
    | some c => c.toNat - '0'.toNat
  else 
    match s.data[0]? with
    | none => 0
    | some c => (c.toNat - '0'.toNat) * 10 + string_to_nat (s.drop 1)

partial def caesar_shift (s : String) (n : Nat) : String :=
  if s.length = 0 then ""
  else
    match s.data[0]? with
    | none => ""
    | some c =>
      let shifted_val := ((c.toNat - 'A'.toNat) + n) % 26
      let shifted_char := Char.ofNat ('A'.toNat + shifted_val)
      String.mk [shifted_char] ++ caesar_shift (s.drop 1) n

def ValidInput (input : String) : Prop :=
  input.length > 0 ∧
  (∃ i, i < input.length ∧ input.data[i]? = some '\n') ∧
  let lines := split_lines input
  lines.length ≥ 2 ∧
  is_valid_number (lines[0]!) ∧
  string_to_nat (lines[0]!) ≤ 26 ∧
  (lines[1]!).length ≥ 1 ∧ (lines[1]!).length ≤ 10000 ∧
  (lines[1]!).all (fun c => 'A' ≤ c ∧ c ≤ 'Z')

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- no helper code needed
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
    let lines := split_lines input
  let n := string_to_nat (lines[0]!)
  let s := lines[1]!
  caesar_shift s n ++ "\n"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  let lines := split_lines input
  let n := string_to_nat (lines[0]!)
  let s := lines[1]!
  result = caesar_shift s n ++ "\n"

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
    simpa [solve_postcond, solve]
-- </vc-theorems>
