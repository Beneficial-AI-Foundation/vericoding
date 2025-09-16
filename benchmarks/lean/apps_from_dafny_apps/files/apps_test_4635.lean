-- <vc-preamble>
def SplitByNewline (s : String) : List String := sorry
def SplitBySpace (s : String) : List String := sorry

def IsValidInteger (s : String) : Prop :=
  s.length > 0 ∧ 
  (s.length = 1 ∨ s.data[0]! ≠ '0' ∨ s = "0") ∧
  ∀ i, i < s.length → '0' ≤ s.data[i]! ∧ s.data[i]! ≤ '9'

def StringToIntVal (s : String) : Int := sorry

def ValidTestCaseLine (line : String) : Prop :=
  ∃ parts, (parts = SplitBySpace line ∧
            parts.length ≥ 2 ∧
            IsValidInteger (parts[0]!) ∧
            IsValidInteger (parts[1]!) ∧
            StringToIntVal (parts[0]!) > 0 ∧
            StringToIntVal (parts[1]!) > 0 ∧
            StringToIntVal (parts[1]!) ≤ 26)

def ValidInput (input : String) : Prop :=
  input.length > 0 ∧ 
  (∃ lines, lines = SplitByNewline input ∧ 
   lines.length ≥ 1 ∧ 
   IsValidInteger (lines[0]!) ∧
   StringToIntVal (lines[0]!) ≥ 0 ∧
   Int.natAbs (lines.length) ≥ Int.natAbs (StringToIntVal (lines[0]!) + 1) ∧
   (∀ i, 1 ≤ i ∧ i ≤ StringToIntVal (lines[0]!) ∧ Int.natAbs i < lines.length → ValidTestCaseLine (lines[Int.natAbs i]!)))

def CyclicPatternCorrect (n : Int) (k : Int) (output : String) : Prop :=
  n > 0 ∧ k > 0 ∧ k ≤ 26 →
  (Int.natAbs output.length = Int.natAbs n ∧
   (∀ j, j < Int.natAbs n → output.data[j]! = Char.ofNat (Int.natAbs ((j % Int.natAbs k) + 97))))

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  ValidInput stdin_input
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
  result.length ≥ 0

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>
