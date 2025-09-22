-- <vc-preamble>
def SplitByNewlines (s : String) : List String :=
  s.splitOn "\n"

def IsNonNegativeInteger (s : String) : Prop :=
  s.length > 0 ∧ ∀ i : Nat, i < s.length → '0' ≤ s.data[i]! ∧ s.data[i]! ≤ '9'

def StringToInt (s : String) : Int :=
  s.toInt!

def IsPositiveInteger (s : String) : Prop :=
  IsNonNegativeInteger s ∧ s.length > 0 ∧ (s.length > 1 ∨ s.data[0]! ≠ '0') ∧ StringToInt s > 0

def ParseIntArray (s : String) : List Int :=
  (s.splitOn " ").map StringToInt

def IsValidXArray (s : String) (n k : Int) : Prop :=
  let x := ParseIntArray s
  x.length = n.natAbs ∧ ∀ i : Nat, i < n.natAbs → 0 < x[i]! ∧ x[i]! < k

def MyMin (a b : Int) : Int :=
  if a ≤ b then a else b

def MySum (xs : List Int) : Int :=
  xs.foldr (· + ·) 0

def ComputeMinDistance (x : List Int) (k : Int) : Int :=
  MySum (x.map (fun xi => 2 * MyMin (k - xi) xi))

def ValidInput (s : String) : Prop :=
  let lines := SplitByNewlines s
  lines.length ≥ 3 ∧
  IsPositiveInteger (lines[0]!) ∧
  IsPositiveInteger (lines[1]!) ∧
  let n := StringToInt (lines[0]!)
  let k := StringToInt (lines[1]!)
  1 ≤ n ∧ n ≤ 100 ∧
  1 ≤ k ∧ k ≤ 100 ∧
  IsValidXArray (lines[2]!) n k

def ValidOutput (result : String) : Prop :=
  result.length ≥ 2 ∧
  result.data[result.length - 1]! = '\n' ∧
  IsNonNegativeInteger (result.take (result.length - 1))

def CorrectSolution (input output : String) : Prop :=
  ValidInput input ∧ ValidOutput output →
    let lines := SplitByNewlines input
    let n := StringToInt (lines[0]!)
    let k := StringToInt (lines[1]!)
    let x := ParseIntArray (lines[2]!)
    x.length = n.natAbs ∧
    (∀ i : Nat, i < n.natAbs → 0 < x[i]! ∧ x[i]! < k) ∧
    let expectedSum := ComputeMinDistance x k
    StringToInt (output.take (output.length - 1)) = expectedSum

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  s.length > 0 ∧ ValidInput s
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result : String) (h_precond : solve_precond s) : Prop :=
  result.length > 0 ∧
  result.data[result.length - 1]! = '\n' ∧
  ValidOutput result ∧
  CorrectSolution s result

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  sorry
-- </vc-theorems>