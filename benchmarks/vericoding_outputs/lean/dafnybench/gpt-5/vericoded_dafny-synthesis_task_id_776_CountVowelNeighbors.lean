import Mathlib
-- <vc-preamble>
def IsVowel (c : Char) : Bool :=
c ∈ ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U']
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma Int.ofNat_ge_zero (n : Nat) : (Int.ofNat n) ≥ 0 :=
  Int.ofNat_nonneg n
-- </vc-helpers>

-- <vc-definitions>
def CountVowelNeighbors (s : String) : Int :=
Int.ofNat (((List.range s.length).filter (fun i =>
  i ≥ 1 ∧ i < s.length - 1 ∧
  IsVowel (s.toList[i-1]!) ∧
  IsVowel (s.toList[i+1]!))).length)
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
  let count := CountVowelNeighbors s
  constructor
  ·
    simpa [count, CountVowelNeighbors] using
      (Int.ofNat_nonneg
        (((List.range s.length).filter (fun i =>
          i ≥ 1 ∧ i < s.length - 1 ∧
          IsVowel (s.toList[i-1]!) ∧
          IsVowel (s.toList[i+1]!))).length))
  ·
    simpa [count, CountVowelNeighbors]
-- </vc-theorems>
