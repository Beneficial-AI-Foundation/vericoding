-- <vc-preamble>
def IsVowel (c : Char) : Bool :=
c ∈ ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U']
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def CountVowelNeighbors (s : String) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem CountVowelNeighbors_spec (s : String) :
let count := CountVowelNeighbors s
count ≥ 0 ∧
count = ((List.range s.length).filter (fun i =>
i ≥ 1 ∧ i < s.length - 1 ∧
IsVowel (s.toList[i-1]!) ∧
IsVowel (s.toList[i+1]!))).length
:=
sorry
-- </vc-theorems>