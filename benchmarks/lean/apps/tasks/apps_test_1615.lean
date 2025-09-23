-- <vc-preamble>
def SplitLines (s : String) : List String := s.splitOn "\n"

def ParsesAsIntegers (_ : String) (_ _ : Int) : Prop := True

def ContainsNewline (s : String) : Bool := s.contains '\n'

def IsNumericOutput (_ : String) : Bool := True

def IntToString (n : Int) : String := toString n

def MaxInt (a b : Int) : Int := max a b

def MinInt (a b : Int) : Int := min a b

def ValidInputFormat (s : String) : Prop :=
  let lines := SplitLines s
  lines.length ≥ 1 ∧
  ∃ n k : Nat, 
      ParsesAsIntegers (lines[0]!) (n : Int) (k : Int) ∧ n > 0 ∧ k > 0 ∧ lines.length ≥ n + 1 ∧
      (∀ i, 1 ≤ i ∧ i ≤ n ∧ i < lines.length → 
          ∃ a b : Int, ParsesAsIntegers (lines[i]!) a b)

def ParsedCorrectly (input : String) (n k : Nat) (segments : List (Int × Int)) : Prop :=
  let lines := SplitLines input
  lines.length ≥ n + 1 ∧ segments.length = n ∧
  ParsesAsIntegers (lines[0]!) (n : Int) (k : Int) ∧
  (∀ i, 0 ≤ i ∧ i < n ∧ i + 1 < lines.length → 
      ParsesAsIntegers (lines[i + 1]!) (segments[i]!).1 (segments[i]!).2)

def stringGetSafe (s : String) (i : Nat) : Char :=
  if h : i < s.length then s.get (String.Pos.mk i) else default

def IsValidOutput (s : String) : Prop :=
  s.length > 0 ∧ 
  stringGetSafe s (s.length - 1) = '\n' ∧ 
  (∀ i, 0 ≤ i ∧ i < s.length - 1 → stringGetSafe s i ≠ '\n') ∧
  IsNumericOutput (s.take (s.length - 1))

def SegmentLength (segment : Int × Int) : Nat :=
  let maxVal := MaxInt segment.1 segment.2
  let minVal := MinInt segment.1 segment.2
  if maxVal ≥ minVal then Int.natAbs (maxVal - minVal + 1) else 1

def TotalCoverage (segments : List (Int × Int)) : Nat :=
  match segments with
  | [] => 0
  | head :: tail => SegmentLength head + TotalCoverage tail

def MinMovesToDivisible (segments : List (Int × Int)) (k : Nat) : Nat :=
  if k = 0 then 0 else
  let totalCoverage := TotalCoverage segments
  let remainder := totalCoverage % k
  if remainder = 0 then 0 else k - remainder

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧
  (stringGetSafe stdin_input (stdin_input.length - 1) = '\n' ∨ ¬ContainsNewline stdin_input)
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
  (result.length = 0 ∨ stringGetSafe result (result.length - 1) = '\n') ∧
  (ValidInputFormat stdin_input → 
      ∃ n k : Nat, ∃ segments : List (Int × Int),
          n > 0 ∧ k > 0 ∧ segments.length = n ∧
          ParsedCorrectly stdin_input n k segments ∧
          result = IntToString (MinMovesToDivisible segments k) ++ "\n") ∧
  (ValidInputFormat stdin_input → IsValidOutput result) ∧
  (¬ValidInputFormat stdin_input → 
      (result = "" ∨ (result.length > 0 ∧ stringGetSafe result (result.length - 1) = '\n')))

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>