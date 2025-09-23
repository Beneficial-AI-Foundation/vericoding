-- <vc-preamble>
-- Helper functions (axiomatized for now)
axiom splitLines : String → List String
axiom extractMFromLine : String → Int
axiom extractN : String → Int
axiom extractM : String → Int
axiom intToString : Int → String
axiom countOnes : String → Int
axiom countDashes : String → Int
axiom intMin : Int → Int → Int
axiom extractQuery : String → Int × Int
axiom joinWithNewlines : List String → String

def containsValidFirstLine (line : String) : Prop :=
  ∃ n m, n ≥ 0 ∧ m ≥ 0 ∧ line = intToString n ++ " " ++ intToString m

def containsValidSecondLine (line : String) : Prop :=
  line.length ≥ 0 ∧
  ∀ c, c ∈ line.toList → c = '1' ∨ c = '-'

def containsValidQuery (line : String) : Prop :=
  ∃ l r, l ≥ 0 ∧ r ≥ l ∧ line = intToString l ++ " " ++ intToString r

def ValidInput (input : String) : Prop :=
  let lines := splitLines input
  lines.length ≥ 2 ∧
  containsValidFirstLine lines[0]! ∧
  containsValidSecondLine lines[1]! ∧
  lines.length = 2 + extractMFromLine lines[0]! ∧
  (∀ i, 2 ≤ i ∧ i < lines.length → containsValidQuery lines[i]!) ∧
  extractN lines[0]! = lines[1]!.length

noncomputable def computeCorrectResult (input : String) : String :=
  let lines := splitLines input
  let m := extractM input
  let arrayLine := lines[1]!
  let positives := countOnes arrayLine
  let negatives := countDashes arrayLine
  let maxBalanceable := 2 * intMin positives negatives
  let outputs := (List.range (Int.natAbs m)).map (fun i =>
    let query := extractQuery lines[i + 2]!
    let l := query.1
    let r := query.2
    let rangeLength := r - l + 1
    if rangeLength % 2 = 0 ∧ rangeLength ≤ maxBalanceable then "1" else "0"
  )
  joinWithNewlines outputs

def endsWithNewlineIfNonEmpty (s : String) : Prop :=
  s.length = 0 ∨ (s.length > 0 ∧ s.data[s.length - 1]! = '\n')

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
def solve_postcond (stdin_input : String) (result : String) (h_precond : solve_precond stdin_input) : Prop :=
  result.length ≥ 0 ∧
  result = computeCorrectResult stdin_input ∧
  (∀ line, line ∈ splitLines result → line = "0" ∨ line = "1") ∧
  (splitLines result).length = extractM stdin_input ∧
  endsWithNewlineIfNonEmpty result

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>