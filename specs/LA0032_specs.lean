-- <vc-preamble>
def ListSum (s : List Int) : Int :=
  s.sum

def ParseInt (s : String) : Int :=
  s.toInt?.getD 0

def CharToDigit (c : Char) : Int :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat else 0

def Power10 (n : Int) : Int :=
  if n ≤ 0 then 1 else 10 * Power10 (n - 1)
  termination_by n.toNat
  decreasing_by simp_wf; omega

def ParseDigits (s : String) : List Int :=
  s.toList.map CharToDigit

def SplitLines (s : String) : List String :=
  s.splitOn "\n"

def SplitByChar (s : String) (delimiter : Char) : List String :=
  s.splitOn delimiter.toString

def Trim (s : String) : String :=
  s.trim

def TrimLeft (s : String) : String :=
  s.trimLeft

def TrimRight (s : String) : String :=
  s.trimRight

axiom CanPartitionRemainder (digits : List Int) (start : Int) (targetSum : Int) : Prop

def CanPartitionIntoEqualSumSegments (input : String) : Prop :=
  let lines := SplitLines input
  if lines.length < 2 then False
  else
    let nStr := Trim lines[0]!
    let digitsStr := Trim lines[1]!
    let n := ParseInt nStr
    if n < 2 ∨ n > 100 ∨ digitsStr.length ≠ n.toNat then False
    else
      let digits := ParseDigits digitsStr
      if digits.length ≠ n.toNat then False
      else
        ∃ i, 0 ≤ i ∧ i < n - 1 ∧ 
          let firstSum := ListSum (digits.take (i + 1).toNat)
          firstSum ≥ 0 ∧
          CanPartitionRemainder digits (i + 1) firstSum

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  s.length > 0
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
  (result = "YES\n" ∨ result = "NO\n") ∧
  (result = "YES\n" ↔ CanPartitionIntoEqualSumSegments s)

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  sorry
-- </vc-theorems>