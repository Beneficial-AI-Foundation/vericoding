-- <vc-preamble>
-- Helper functions (assumed to exist)
noncomputable axiom splitLines : String → List String
axiom parseInteger : String → Nat
axiom countSizes : List String → List String
axiom countUnmatchedSizes : List String → List String → Nat
axiom intToString : Nat → String

def validInput (stdin_input : String) : Prop :=
  let lines := splitLines stdin_input
  lines.length ≥ 1 ∧ 
  (let n := parseInteger (lines[0]!)
   lines.length ≥ 2*n + 1 ∧ 
   (∀ i : Nat, 1 ≤ i ∧ i ≤ 2*n → i < lines.length ∧ (lines[i]!).length > 0))

noncomputable def computeMismatches (stdin_input : String) : Nat :=
  let lines := splitLines stdin_input
  let n := parseInteger (lines[0]!)
  if n = 0 then 0
  else
    let prevSizes := countSizes ((lines.drop 1).take n)
    let currentSizes := (lines.drop (n+1)).take n
    countUnmatchedSizes prevSizes currentSizes

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧ validInput stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
noncomputable def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (h_precond : solve_precond stdin_input) : Prop :=
  result.length > 0 ∧
  (result.data.getLast! = '\n' ∨ (result.length > 1 ∧ result.drop (result.length-2) = "\r\n")) ∧
  (∃ mismatches : Nat, result = intToString mismatches ++ "\n" ∧ 
   mismatches = computeMismatches stdin_input) ∧
  (let lines := splitLines stdin_input
   let n := parseInteger (lines[0]!)
   let mismatches := computeMismatches stdin_input
   mismatches ≤ n ∧
   result = intToString mismatches ++ "\n")

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>