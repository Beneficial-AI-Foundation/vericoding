import Mathlib
-- <vc-preamble>
def ContainsLowercase (s: String) : Bool :=
  s.data.any fun c => 'a' ≤ c && c ≤ 'z'

def ContainsUppercase (s: String) : Bool :=
  s.data.any fun c => 'A' ≤ c && c ≤ 'Z'

def ContainsDigit (s: String) : Bool :=
  s.data.any fun c => '0' ≤ c && c ≤ '9'

def IsValidPassword (s: String) : Bool :=
  s.length ≥ 5 && ContainsLowercase s && ContainsUppercase s && ContainsDigit s

def TrimNewline (s: String) : String :=
  if s.length > 0 && s.data[s.length - 1]! = '\n' then
    ⟨s.data.take (s.length - 1)⟩
  else s

def StripWhitespace (s: String) : String :=
  let chars := s.data
  let trimmed := chars.dropWhile fun c => c = ' ' || c = '\t' || c = '\n' || c = '\r'
  let result := trimmed.reverse.dropWhile fun c => c = ' ' || c = '\t' || c = '\n' || c = '\r'
  ⟨result.reverse⟩

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: no additional helpers required
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  let processedInput := TrimNewline input
  let stripped := StripWhitespace processedInput
  if IsValidPassword stripped then
    "Correct\n"
  else
    "Too weak\n"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (output: String) (h_precond : solve_precond input) : Prop :=
  let processedInput := TrimNewline input
  let stripped := StripWhitespace processedInput
  if IsValidPassword stripped then
    output = "Correct\n"
  else
    output = "Too weak\n"

theorem solve_spec_satisfied (input: String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  classical
  by_cases h : IsValidPassword (StripWhitespace (TrimNewline input)) <;>
    simp [solve_postcond, solve, h]
-- </vc-theorems>
