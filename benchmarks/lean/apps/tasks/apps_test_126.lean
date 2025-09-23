-- <vc-preamble>
def string_to_digits (s : String) : List Int :=
  let chars := s.toList
  let indices := List.range chars.length
  let digit_indices := indices.filter (fun i => 
    let c := chars[i]!
    '0' ≤ c ∧ c ≤ '9')
  digit_indices.map (fun i => 
    let c := chars[i]!
    (c.toNat - '0'.toNat : Int))

def ValidInput (input : String) : Prop :=
  input.length > 0 ∧ input.contains '\n'

def HasUniqueMovementSequence (digits : List Int) : Prop :=
  (1 ∈ digits ∨ 4 ∈ digits ∨ 7 ∈ digits ∨ 0 ∈ digits) ∧
  (1 ∈ digits ∨ 2 ∈ digits ∨ 3 ∈ digits) ∧
  (3 ∈ digits ∨ 6 ∈ digits ∨ 9 ∈ digits ∨ 0 ∈ digits) ∧
  (7 ∈ digits ∨ 0 ∈ digits ∨ 9 ∈ digits)

def find_char (s : String) (c : Char) : Int :=
  let idx := s.toList.findIdx (· = c)
  if idx < s.length then idx else -1

def split_lines (s : String) : List String :=
  s.splitOn "\n"

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
  (result = "YES\n" ∨ result = "NO\n") ∧
  result.length > 0 ∧
  (let lines := split_lines input
   lines.length ≥ 2 →
   let digits_str := lines[1]!
   let digits := string_to_digits digits_str
   (result = "YES\n" ↔ HasUniqueMovementSequence digits))

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>