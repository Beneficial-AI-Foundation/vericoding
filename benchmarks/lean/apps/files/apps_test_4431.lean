-- <vc-preamble>
def ValidInput (n k : Nat) (s : String) (available : List Char) : Prop :=
  n = s.length ∧
  k = available.length ∧
  ∀ i j, 0 ≤ i ∧ i < j ∧ j < available.length → available[i]! ≠ available[j]!

def SumSegmentCounts : List Nat → Nat
  | [] => 0
  | h :: t => h * (h + 1) / 2 + SumSegmentCounts t

def GetNextSegmentLength (s : String) (availableSet : List Char) (startIdx : Nat) : Nat :=
  if startIdx ≥ s.length then 0
  else if s.data[startIdx]! ∉ availableSet then 0
  else 1 + GetNextSegmentLength s availableSet (startIdx + 1)

def SkipInvalidChars (s : String) (availableSet : List Char) (startIdx : Nat) : Nat :=
  if startIdx ≥ s.length then 0
  else if s.data[startIdx]! ∈ availableSet then 0
  else 1 + SkipInvalidChars s availableSet (startIdx + 1)

def GetMaximalValidSegments (s : String) (availableSet : List Char) (startIdx : Nat) : List Nat :=
  if startIdx ≥ s.length then []
  else
    let segmentLength := GetNextSegmentLength s availableSet startIdx
    if segmentLength = 0 then
      GetMaximalValidSegments s availableSet (startIdx + 1)
    else
      let skipLength := SkipInvalidChars s availableSet (startIdx + segmentLength)
      let nextIdx := startIdx + segmentLength + skipLength
      if nextIdx ≤ s.length then
        segmentLength :: GetMaximalValidSegments s availableSet nextIdx
      else
        [segmentLength]

def CountValidSubstrings (s : String) (availableSet : List Char) : Nat :=
  if s.length = 0 then 0
  else
    let segments := GetMaximalValidSegments s availableSet 0
    SumSegmentCounts segments

@[reducible, simp]
def solve_precond (n k : Nat) (s : String) (available : List Char) : Prop :=
  ValidInput n k s available
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Nat) (s : String) (available : List Char) (h_precond : solve_precond n k s available) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Nat) (s : String) (available : List Char) (result : Nat) (h_precond : solve_precond n k s available) : Prop :=
  result ≤ n * (n + 1) / 2 ∧
  result = CountValidSubstrings s available

theorem solve_spec_satisfied (n k : Nat) (s : String) (available : List Char) (h_precond : solve_precond n k s available) :
    solve_postcond n k s available (solve n k s available h_precond) h_precond := by
  sorry
-- </vc-theorems>