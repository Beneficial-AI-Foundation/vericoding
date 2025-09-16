-- <vc-preamble>
-- <vc-preamble>
def SplitByNewlines (s : String) : List String := sorry
def StringToInt (s : String) : Int := sorry
def ParseIntArray (s : String) : List Int := sorry
def ListSum (xs : List Int) : Int := sorry
def IntMin (a b : Int) : Int := sorry

def IsNonNegativeInteger (s : String) : Prop :=
  s.length > 0 ∧ ∀ i, 0 ≤ i ∧ i < s.length → '0' ≤ s.data[i]! ∧ s.data[i]! ≤ '9'

def IsPositiveInteger (s : String) : Prop :=
  IsNonNegativeInteger s ∧ s.length > 0 ∧ (s.length > 1 ∨ s.data[0]! ≠ '0') ∧ StringToInt s > 0

def IsValidXArray (s : String) (n k : Int) : Prop :=
  let x := ParseIntArray s
  x.length = Int.natAbs n ∧ ∀ i, 0 ≤ i ∧ i < n → 0 < x[Int.natAbs i]! ∧ x[Int.natAbs i]! < k

def ComputeMinDistance (x : List Int) (k : Int) : Int :=
  ListSum (x.map (fun xi => 2 * IntMin (k - xi) xi))

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
  x.length = Int.natAbs n ∧
  (∀ i, 0 ≤ i ∧ i < n → 0 < x[Int.natAbs i]! ∧ x[Int.natAbs i]! < k) ∧
  let expectedSum := ComputeMinDistance x k
  StringToInt (output.take (output.length - 1)) = expectedSum

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  s.length > 0 ∧ ValidInput s
-- </vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : String :=
  sorry
-- </vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>
