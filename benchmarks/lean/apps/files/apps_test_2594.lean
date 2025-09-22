-- <vc-preamble>
-- Placeholder functions for string parsing operations
def SplitLines (input : String) : List String := [input]
def SplitSpaces (line : String) : List String := [line]
def ParseInt (s : String) : Int := 0

def ValidInput (input : String) : Prop :=
  let lines := SplitLines input
  lines.length > 0 ∧
  let t := ParseInt (lines[0]!)
  t > 0 ∧ lines.length ≥ Int.natAbs t + 1 ∧
  ∀ i : Nat, i < Int.natAbs t →
    let parts := SplitSpaces (lines[i + 1]!)
    parts.length ≥ 2 ∧
    let n := ParseInt (parts[0]!)
    let m := ParseInt (parts[1]!)
    n ≥ 1 ∧ m ≥ 1

def MinLanterns (n m : Int) : Int :=
  (n * m + 1) / 2

def ValidOutput (input : String) (output : List Int) : Prop :=
  let lines := SplitLines input
  let t := ParseInt (lines[0]!)
  output.length = Int.natAbs t ∧
  ∀ i : Nat, i < Int.natAbs t →
    let parts := SplitSpaces (lines[i + 1]!)
    parts.length ≥ 2 ∧
    let n := ParseInt (parts[0]!)
    let m := ParseInt (parts[1]!)
    n ≥ 1 ∧ m ≥ 1 ∧
    output[i]! = MinLanterns n m

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : List Int) (h_precond : solve_precond input) : Prop :=
  ValidOutput input result

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>