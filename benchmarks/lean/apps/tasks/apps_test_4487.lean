-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length > 0

def ValidParsedInput (parts : List String) : Prop :=
  parts.length = 3 ∧ parts[0]!.length > 0 ∧ parts[1]!.length > 0 ∧ parts[2]!.length > 0

def IsWordChain (a b c : String) : Prop :=
  a.length > 0 ∧ b.length > 0 ∧ c.length > 0 →
  (a.back = b.front) ∧ (b.back = c.front)

def SplitOnSpaces (s : String) : List String := 
  s.split (· = ' ')

def ExpectedResult (input : String) : String :=
  let stripped := if input.length > 0 ∧ input.back = '\n' 
                 then input.dropRight 1
                 else input
  let parts := SplitOnSpaces stripped
  if parts.length = 3 ∧ parts[0]!.length > 0 ∧ parts[1]!.length > 0 ∧ parts[2]!.length > 0 then
    if parts[0]!.length > 0 ∧ parts[1]!.length > 0 ∧ parts[2]!.length > 0 ∧ 
       (parts[0]!.back = parts[1]!.front) ∧ (parts[1]!.back = parts[2]!.front) then 
      "YES\n" 
    else 
      "NO\n"
  else ""

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
  result = ExpectedResult input ∧ (result = "YES\n" ∨ result = "NO\n" ∨ result = "")

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>