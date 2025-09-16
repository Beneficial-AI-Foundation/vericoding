-- <vc-preamble>
def ParseLines (stdin_input : String) : List String :=
  sorry

def FindNewline (s : String) (start : Int) : Int :=
  sorry

def ValidInput (stdin_input : String) : Prop :=
  let lines := ParseLines stdin_input
  lines.length ≥ 2 ∧ lines.length > 0 ∧ lines.length > 1 ∧
  lines[0]!.length > 0 ∧ lines[1]!.length > 0 ∧
  (∀ c, c ∈ lines[0]!.toList → 'a' ≤ c ∧ c ≤ 'z') ∧
  (∀ c, c ∈ lines[1]!.toList → 'a' ≤ c ∧ c ≤ 'z')

def IsSubsequence (s t : String) : Bool :=
  sorry

def SortString (s : String) : String :=
  sorry

def FilterChars (s : String) (pivot : Char) (takeLess takeEqual : Bool) : String :=
  sorry

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧ ValidInput stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result: String) (h_precond : solve_precond stdin_input) : Prop :=
  result ∈ ["array", "automaton", "both", "need tree"] ∧
  let lines := ParseLines stdin_input
  let s := lines[0]!
  let t := lines[1]!
  let sx := SortString s
  let tx := SortString t
  ((sx = tx ∧ result = "array") ∨
   (sx ≠ tx ∧ IsSubsequence t s ∧ result = "automaton") ∨
   (sx ≠ tx ∧ ¬IsSubsequence t s ∧ IsSubsequence tx sx ∧ result = "both") ∨
   (sx ≠ tx ∧ ¬IsSubsequence t s ∧ ¬IsSubsequence tx sx ∧ result = "need tree"))

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>
