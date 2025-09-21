-- <vc-preamble>
def SplitByNewlineSpec (_ : String) : List String := []
def SplitBySpaceSpec (_ : String) : List String := []
def ParseIntSpec (_ : String) : Int := 0
def IntToString (_ : Int) : String := ""

def ValidInput (input : String) : Prop :=
  let lines := SplitByNewlineSpec input
  lines.length ≥ 2 ∧
  let firstLine := SplitBySpaceSpec (lines[0]!)
  firstLine.length ≥ 2 ∧
  let N := ParseIntSpec (firstLine[0]!)
  let x := ParseIntSpec (firstLine[1]!)
  N ≥ 2 ∧ x ≥ 0 ∧
  let secondLine := SplitBySpaceSpec (lines[1]!)
  secondLine.length = N.natAbs ∧
  (∀ i, 0 ≤ i ∧ i < N → ParseIntSpec (secondLine[i.natAbs]!) ≥ 0)

def ComputeOperationsFromIndex (originalA : List Int) (x : Int) (index : Nat) (currentA : List Int) (currentCount : Int) : Int :=
  if index ≥ originalA.length then currentCount
  else
    let newValue := if currentA[index]! + currentA[index-1]! > x then x - currentA[index-1]! else currentA[index]!
    let additionalOps := if currentA[index]! + currentA[index-1]! > x then currentA[index]! + currentA[index-1]! - x else 0
    let newA := currentA.set index newValue
    ComputeOperationsFromIndex originalA x (index + 1) newA (currentCount + additionalOps)
termination_by originalA.length - index

def ComputeMinimumOperations (A : List Int) (x : Int) : Int :=
  if A.length ≥ 2 ∧ x ≥ 0 ∧ (∀ a ∈ A, a ≥ 0) then
    let A0 := if A[0]! > x then x else A[0]!
    let cnt0 := if A[0]! > x then A[0]! - x else 0
    ComputeOperationsFromIndex A x 1 (A0 :: A.tail) cnt0
  else 0

def MinimumCandiesNeeded (input : String) (h : ValidInput input) : Int :=
  let lines := SplitByNewlineSpec input
  let firstLine := SplitBySpaceSpec (lines[0]!)
  let N := ParseIntSpec (firstLine[0]!)
  let x := ParseIntSpec (firstLine[1]!)
  let secondLine := SplitBySpaceSpec (lines[1]!)
  let A := List.range N.natAbs |>.map (fun i => ParseIntSpec (secondLine[i]!))
  ComputeMinimumOperations A x

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0 ∧ ValidInput input
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
  result.length > 0 ∧ result = IntToString (MinimumCandiesNeeded input h_precond.2) ++ "\n"

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>