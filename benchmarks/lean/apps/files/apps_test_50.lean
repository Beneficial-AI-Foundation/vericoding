-- <vc-preamble>
def ValidIntLine (line : String) (expectedCount : Option Nat := none) : Bool :=
  True

def SplitLinesFunc (input : String) : List String :=
  input.splitOn "\n"

def SplitIntsFunc (line : String) : List Int :=
  []

def MinSeqFunc (S : List Int) : Int :=
  match S with
  | [] => 1
  | x :: xs => S.foldl min x

def MaxSeqFunc (B : List Int) : Int :=
  match B with
  | [] => 1
  | x :: xs => B.foldl max x

def IntToStringFunc (n : Int) : String :=
  toString n

def ValidInput (input : String) : Prop :=
  input.length > 0 ∧ '\n' ∈ input.toList ∧
  let lines := SplitLinesFunc input
  lines.length ≥ 3 ∧
  ValidIntLine lines[0]! = true ∧
  ValidIntLine lines[1]! = true ∧
  ValidIntLine lines[2]! = true ∧
  let firstLine := SplitIntsFunc lines[0]!
  let S := SplitIntsFunc lines[1]!
  let B := SplitIntsFunc lines[2]!
  firstLine.length = 3 ∧ firstLine[0]! ≥ 1 ∧ firstLine[1]! ≥ 1 ∧ firstLine[2]! ≥ 1 ∧
  S.length = firstLine[0]! ∧ B.length = firstLine[1]!

def ParseInput (input : String) : (Int × Int × Int × List Int × List Int) :=
  let lines := SplitLinesFunc input
  let firstLine := SplitIntsFunc lines[0]!
  let S := SplitIntsFunc lines[1]!
  let B := SplitIntsFunc lines[2]!
  (firstLine[0]!, firstLine[1]!, firstLine[2]!, S, B)

def ComputeMaxBourles (r : Int) (S B : List Int) : Int :=
  let x := MinSeqFunc S
  let y := MaxSeqFunc B
  let cnt := (r % x) + (r / x) * y
  if r > cnt then r else cnt

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0 ∧ '\n' ∈ input.toList ∧ ValidInput input
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
  result.length > 0 ∧
  ∃ n m r S B,
    ParseInput input = (n, m, r, S, B) ∧
    n ≥ 1 ∧ m ≥ 1 ∧ r ≥ 1 ∧
    S.length = n ∧ B.length = m ∧
    (∀ i, 0 ≤ i ∧ i < S.length → S[i]! ≥ 1) ∧
    (∀ i, 0 ≤ i ∧ i < B.length → B[i]! ≥ 1) ∧
    result = IntToStringFunc (ComputeMaxBourles r S B) ++ "\n"

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>