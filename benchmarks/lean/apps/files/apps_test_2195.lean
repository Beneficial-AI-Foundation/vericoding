-- <vc-preamble>
def SplitByChar (s : String) (delimiter : Char) : List String :=
  s.split (· = delimiter)

def SplitLines (s : String) : List String :=
  if s.length = 0 then []
  else SplitByChar s '\n'

def SplitWhitespace (s : String) : List String :=
  if s.length = 0 then []
  else SplitByChar s ' '

def StringToIntHelper (s : String) : Int :=
  s.toInt?.getD 0

def StringToInt (s : String) : Int :=
  if s.length = 0 then 0
  else if s.length > 0 ∧ s.get! 0 = '-' ∧ s.length > 1 then -(StringToIntHelper (s.drop 1))
  else StringToIntHelper s

def IntToStringHelper (n : Nat) : String :=
  if n = 0 then ""
  else IntToStringHelper (n / 10) ++ String.mk [Char.ofNat ((n % 10) + ('0').toNat)]

def IntToString (n : Int) : String :=
  if n = 0 then "0"
  else if n < 0 then "-" ++ IntToStringHelper (Int.natAbs n)
  else IntToStringHelper (Int.natAbs n)

def IsValidInteger (s : String) : Prop :=
  s.length > 0 ∧
  (s.length > 0 ∧ s.get! 0 = '-' → s.length > 1) ∧
  ∀ i, (if s.length > 0 ∧ s.get! 0 = '-' then 1 else 0) ≤ i ∧ i < s.length → 
    '0' ≤ s.data.get! i ∧ s.data.get! i ≤ '9'

def ValidInput (input : String) : Prop :=
  let lines := SplitLines input
  lines.length ≥ 1 ∧
  (lines.length > 0 → IsValidInteger (lines[0]!)) ∧
  let t := if lines.length > 0 then StringToInt (lines[0]!) else 0
  t ≥ 0 ∧
  lines.length ≥ 1 + 2 * Int.natAbs t ∧
  ∀ i, 0 ≤ i ∧ i < t →
    (Int.natAbs (1 + 2*i) + 1 < lines.length ∧ 
     (SplitWhitespace (lines[Int.natAbs (1 + 2*i)]!)).length ≥ 2 ∧
     Int.natAbs (1 + 2*i) + 2 < lines.length ∧ 
     (SplitWhitespace (lines[Int.natAbs (1 + 2*i) + 1]!)).length ≥ 2 ∧
     IsValidInteger ((SplitWhitespace (lines[Int.natAbs (1 + 2*i)]!))[0]!) ∧
     IsValidInteger ((SplitWhitespace (lines[Int.natAbs (1 + 2*i)]!))[1]!) ∧
     IsValidInteger ((SplitWhitespace (lines[Int.natAbs (1 + 2*i) + 1]!))[0]!) ∧
     IsValidInteger ((SplitWhitespace (lines[Int.natAbs (1 + 2*i) + 1]!))[1]!) ∧
     StringToInt ((SplitWhitespace (lines[Int.natAbs (1 + 2*i)]!))[0]!) ≥ 0 ∧
     StringToInt ((SplitWhitespace (lines[Int.natAbs (1 + 2*i)]!))[1]!) ≥ 0 ∧
     StringToInt ((SplitWhitespace (lines[Int.natAbs (1 + 2*i) + 1]!))[0]!) ≥ 1 ∧
     StringToInt ((SplitWhitespace (lines[Int.natAbs (1 + 2*i) + 1]!))[1]!) ≥ 1)

def ValidOutput (output : String) (input : String) : Prop :=
  let lines := SplitLines input
  if lines.length = 0 then output = ""
  else
    let t := if lines.length > 0 then StringToInt (lines[0]!) else 0
    let outputLines := if output = "" then [] else SplitLines output
    outputLines.length = (if t = 0 then 0 else Int.natAbs t) ∧
    ∀ i, 0 ≤ i ∧ i < outputLines.length → IsValidInteger (outputLines[i]!)

def CorrectComputation (input : String) (output : String) : Prop :=
  let lines := SplitLines input
  if lines.length = 0 then output = ""
  else
    let t := if lines.length > 0 then StringToInt (lines[0]!) else 0
    let outputLines := if output = "" then [] else SplitLines output
    outputLines.length = (if t = 0 then 0 else Int.natAbs t) ∧
    ∀ i, 0 ≤ i ∧ i < t ∧ Int.natAbs (1 + 2*i) + 1 < lines.length →
      let xyLine := SplitWhitespace (lines[Int.natAbs (1 + 2*i)]!)
      let abLine := SplitWhitespace (lines[Int.natAbs (1 + 2*i) + 1]!)
      (xyLine.length ≥ 2 ∧ abLine.length ≥ 2) →
        let x := StringToInt (xyLine[0]!)
        let y := StringToInt (xyLine[1]!)
        let a := StringToInt (abLine[0]!)
        let b := StringToInt (abLine[1]!)
        let expectedResult := if b ≤ 2 * a then
          b * (if x ≤ y then x else y) + (if x ≥ y then x else y - if x ≤ y then x else y) * a
        else
          a * (x + y)
        Int.natAbs i < outputLines.length ∧ StringToInt (outputLines[Int.natAbs i]!) = expectedResult

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
  ValidOutput result input ∧ CorrectComputation input result

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>