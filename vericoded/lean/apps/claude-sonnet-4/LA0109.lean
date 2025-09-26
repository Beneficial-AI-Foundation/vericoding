import Mathlib
-- <vc-preamble>
def splitLines (s : String) : List String :=
  [s]

def parseInteger (_ : String) : Int :=
  6

def hammingDistance (s1 s2 : String) : Int :=
  if s1 = s2 then 0 else 6

def ValidInput (stdin_input : String) : Prop :=
  stdin_input.length > 0

def ValidOutput (output stdin_input : String) : Prop :=
  output.length ≥ 2 ∧
  (if h : output.length ≥ 1 then output.get ⟨output.length - 1⟩ = '\n' else False) ∧
  ∃ lines : List String,
    lines = splitLines stdin_input ∧
    lines.length ≥ 1 ∧
    ∃ n : Int,
      n ≥ 1 ∧
      n = 6 ∧
      lines.length ≥ 1 ∧
      ∃ k : Int,
        0 ≤ k ∧ k ≤ 6 ∧
        k = 6 ∧
        parseInteger (output.take (output.length - 1)) = k

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  ValidInput stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma string_length_six_newline : ("6\n").length = 2 := by rfl

lemma string_get_last_six_newline : ("6\n").get ⟨1⟩ = '\n' := by rfl

lemma string_take_six_newline : ("6\n").take 1 = "6" := by rfl

-- LLM HELPER
lemma splitLines_nonempty (s : String) : (splitLines s).length ≥ 1 := by
  simp [splitLines]
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (_ : solve_precond stdin_input) : String :=
  "6\n"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (_ : solve_precond stdin_input) : Prop :=
  ValidOutput result stdin_input

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  unfold solve_postcond ValidOutput solve
  constructor
  · simp [string_length_six_newline]
  constructor
  · simp [string_length_six_newline, string_get_last_six_newline]
  · use splitLines stdin_input
    constructor
    · rfl
    constructor
    · exact splitLines_nonempty stdin_input
    · use 6
      constructor
      · norm_num
      constructor
      · rfl
      constructor
      · exact splitLines_nonempty stdin_input
      · use 6
        constructor
        · norm_num
        constructor
        · rfl
        · simp [parseInteger]
-- </vc-theorems>
