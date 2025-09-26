import Mathlib
-- <vc-preamble>
-- Placeholder function definitions since axioms are not allowed in preamble
def splitFunc (input : String) (delimiter : Char) : List String := []

def parseIntFunc (s : String) : Int := 0

def processTestCasesHelper (input : String) (lines : List String) (lineIndex : Int) (caseIndex : Int) (totalCases : Int) (acc : List Int) : List Int := []

def formatOutputHelper (results : List Int) (index : Int) (acc : String) : String := ""

def validInput (input : String) : Prop :=
  input.length > 0 ∧ 
  let lines := splitFunc input '\n'
  lines.length ≥ 1 ∧
  parseIntFunc (lines.get! 0) ≥ 0 ∧
  lines.length ≥ 1 + 3 * parseIntFunc (lines.get! 0)

def processTestCases (input : String) (h : validInput input) : List Int :=
  let lines := splitFunc input '\n'
  let t := parseIntFunc (lines.get! 0)
  processTestCasesHelper input lines 1 0 t []

def formatOutput (results : List Int) : String :=
  formatOutputHelper results 0 ""

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0 ∧ validInput input
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Basic lemma about string length
lemma string_length_nonneg (s : String) : s.length ≥ 0 := by
  exact Nat.zero_le s.length
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  formatOutput (processTestCases input h_precond.2)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result.length ≥ 0 ∧ result = formatOutput (processTestCases input (h_precond.2))

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  unfold solve_postcond solve
  constructor
  · exact string_length_nonneg _
  · rfl
-- </vc-theorems>
