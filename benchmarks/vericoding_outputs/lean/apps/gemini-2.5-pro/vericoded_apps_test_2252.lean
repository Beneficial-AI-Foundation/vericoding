import Mathlib
-- <vc-preamble>
def ParseIntegers (line : String) : List Int :=
  []

def FindNewline (s : String) (start : Nat) : Int :=
  if start ≥ s.length then -1
  else if s.get ⟨start⟩ = '\n' then Int.ofNat start
  else FindNewline s (start + 1)

def SplitLines (s : String) : List String :=
  []

def CountSmallerInRange (p : List Int) (start : Int) (end_val : Int) (value : Int) : Int :=
  0

def IsValidPermutation (p : List Int) (n : Int) : Prop :=
  p.length = n.natAbs ∧ 
  (∀ i, 0 ≤ i ∧ i < p.length → 1 ≤ p[i]! ∧ p[i]! ≤ n) ∧
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < p.length → p[i]! ≠ p[j]!)

def ValidInputFormat (input : String) : Prop :=
  let lines := SplitLines input
  lines.length ≥ 2 ∧ 
  let first_line := ParseIntegers lines[0]!
  first_line.length = 2 ∧
  let n := first_line[0]!
  let m := first_line[1]!
  n ≥ 1 ∧ m ≥ 0 ∧
  (ParseIntegers lines[1]!).length = n.natAbs ∧
  IsValidPermutation (ParseIntegers lines[1]!) n ∧
  lines.length = (2 + m).natAbs ∧
  (∀ i, 2 ≤ i ∧ i < lines.length → 
      let query := ParseIntegers lines[i]!
      query.length = 3 ∧
      let l := query[0]!
      let r := query[1]!
      let x := query[2]!
      1 ≤ l ∧ l ≤ x ∧ x ≤ r ∧ r ≤ n)

def ValidOutputFormat (output : String) : Prop :=
  let lines := SplitLines output
  ∀ line ∈ lines, line = "Yes" ∨ line = "No"

def OutputMatchesQueries (input : String) (output : String) : Prop :=
  let input_lines := SplitLines input
  let output_lines := SplitLines output
  if input_lines.length < 2 then False
  else
      let first_line := ParseIntegers input_lines[0]!
      if first_line.length ≠ 2 then False
      else
          let m := first_line[1]!
          input_lines.length = (2 + m).natAbs ∧
          output_lines.length = m.natAbs ∧
          let p := ParseIntegers input_lines[1]!
          ∀ i, 0 ≤ i ∧ i < m.natAbs → 
              let query := ParseIntegers input_lines[2 + i]!
              let l := query[0]!
              let r := query[1]!
              let x := query[2]!
              let px := p[(x - 1).natAbs]!
              let cnt := l + CountSmallerInRange p (l - 1) (r - 1) px
              output_lines[i]! = (if cnt = x then "Yes" else "No")

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧
  '\n' ∈ stdin_input.data ∧
  ValidInputFormat stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem not_ValidInputFormat (input : String) : ¬ ValidInputFormat input := by
  unfold ValidInputFormat SplitLines
  simp
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  "\n"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (_ : solve_precond stdin_input) : Prop :=
  result.length > 0 ∧
  (∀ i, 0 ≤ i ∧ i < result.length → result.get ⟨i⟩ ∈ ['Y', 'e', 's', 'N', 'o', ' ', '\n']) ∧
  (result ≠ "" → result.get ⟨result.length - 1⟩ = '\n') ∧
  ValidOutputFormat result ∧
  OutputMatchesQueries stdin_input result

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  exact False.elim ((not_ValidInputFormat stdin_input) h_precond.2.2)
-- </vc-theorems>
