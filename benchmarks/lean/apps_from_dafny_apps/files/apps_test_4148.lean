-- <vc-preamble>
def split_lines (input : String) : List String :=
  sorry

def find_newline (input : String) (start : Int) : Int :=
  sorry

def is_valid_number (s : String) : Bool :=
  s.length > 0 && (∀ i : Nat, i < s.length → '0' ≤ s.data[i]! ∧ s.data[i]! ≤ '9')

def string_to_nat (s : String) : Nat :=
  sorry

def caesar_shift (s : String) (n : Nat) : String :=
  sorry

def ValidInput (input : String) : Prop :=
  input.length > 0 ∧
  (∃ i : Nat, i < input.length ∧ input.data[i]! = '\n') ∧
  let lines := split_lines input
  lines.length ≥ 2 ∧
  is_valid_number lines[0]! ∧
  string_to_nat lines[0]! ≤ 26 ∧
  lines[1]!.length ≥ 1 ∧ lines[1]!.length ≤ 10000 ∧
  (∀ j : Nat, j < lines[1]!.length → 'A' ≤ lines[1]!.data[j]! ∧ lines[1]!.data[j]! ≤ 'Z')

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  let lines := split_lines input
  let n := string_to_nat lines[0]!
  let s := lines[1]!
  result = caesar_shift s n ++ "\n"

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>
