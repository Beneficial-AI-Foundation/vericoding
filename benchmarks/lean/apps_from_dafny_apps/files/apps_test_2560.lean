-- <vc-preamble>
-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length > 0

def CanMakeSum (n l r : Int) : Bool :=
  l > 0 && l ≤ r && n > 0 && n % l ≤ (r - l) * (n / l)

def ValidOutput (result : String) : Prop :=
  result.length ≥ 0 ∧ ∀ i : Nat, i < result.length → result.data[i]! ∈ ['Y', 'e', 's', '\n', 'N', 'o', ' ']

def SplitLines (s : String) : List String := sorry

def ParseInt (s : String) : Int := sorry

def SplitSpaces (s : String) : List String := sorry

def CorrectSolution (input result : String) : Prop :=
  let lines := SplitLines input
  lines.length > 0 →
  (let t := ParseInt (lines[0]!)
   let outputLines := SplitLines result
   outputLines.length ≥ 1 ∧ (outputLines.length = 1 → outputLines[0]! = "") ∧
   (outputLines.length > 1 → outputLines[outputLines.length - 1]! = "") ∧
   ∀ i : Int, 1 ≤ i ∧ i ≤ t ∧ i.natAbs < lines.length →
     (let parts := SplitSpaces (lines[i.natAbs]!)
      parts.length ≥ 3 →
      (let n := ParseInt (parts[0]!)
       let l := ParseInt (parts[1]!)
       let r := ParseInt (parts[2]!)
       let expectedOutput := if CanMakeSum n l r then "Yes" else "No"
       (i - 1).natAbs < outputLines.length ∧ outputLines[(i - 1).natAbs]! = expectedOutput)))

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  ValidOutput result ∧ CorrectSolution input result

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- </vc-theorems>
