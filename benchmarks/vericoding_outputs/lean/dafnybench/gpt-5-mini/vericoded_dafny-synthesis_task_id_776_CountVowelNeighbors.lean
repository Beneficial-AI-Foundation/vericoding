import Mathlib
-- <vc-preamble>
def IsVowel (c : Char) : Bool :=
c ∈ ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U']
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- Re-export small helper about Int.ofNat nonnegativity
-- LLM HELPER
theorem Int_ofNat_nonneg' (n : Nat) : (Int.ofNat n) ≥ 0 :=
  Int.natCast_nonneg n
-- </vc-helpers>

-- <vc-definitions>
def CountVowelNeighbors (s : String) : Int :=
Int.ofNat ((List.range s.length).filter fun i =>
    i ≥ 1 ∧ i < s.length - 1 ∧
    IsVowel (s.toList[i-1]!) ∧
    IsVowel (s.toList[i+1]!)).length
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
by
  dsimp [CountVowelNeighbors]
  constructor
  · apply Int_ofNat_nonneg'
  · rfl
-- </vc-theorems>
