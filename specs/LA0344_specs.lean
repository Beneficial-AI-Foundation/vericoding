-- <vc-preamble>
-- Helper function for parsing integers (assumed)
axiom parseIntHelper : String → Int → Int → Int

def ValidInput (input : List String) : Prop :=
  input.length ≥ 2 ∧
  let n := parseIntHelper input[0]! 0 0
  n ≥ 1 ∧ n + 1 < input.length

def buildExpectedPattern : List String → List Char
  | [] => ['<', '3']
  | head :: tail => ['<', '3'] ++ head.toList ++ buildExpectedPattern tail
termination_by words => words.length

-- Noncomputable functions for subsequence check
noncomputable axiom isSubsequenceHelper : List Char → List Char → Nat → Nat → Bool

noncomputable def isSubsequence (pattern : List Char) (text : String) : Bool :=
  isSubsequenceHelper pattern text.toList 0 0

@[reducible, simp]
def solve_precond (input : List String) : Prop :=
  input.length ≥ 2 ∧ ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : List String) (_ : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : List String) (result : String) (h_precond : solve_precond input) : Prop :=
  (result = "yes" ∨ result = "no") ∧
  (result = "yes" ↔ (
    ValidInput input ∧
    let n := parseIntHelper input[0]! 0 0
    let nNat := Int.natAbs n
    let expected := buildExpectedPattern ((input.drop 1).take nNat)
    let message := input[nNat + 1]!
    isSubsequence expected message
  ))

theorem solve_spec_satisfied (input : List String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>