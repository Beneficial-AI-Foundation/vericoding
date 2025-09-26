import Mathlib
-- <vc-preamble>

namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def compareNats (n1 n2 : Nat) : Int :=
  if n1 < n2 then -1
  else if n1 = n2 then 0
  else 1
-- </vc-helpers>


-- <vc-definitions>
def Compare (s1 s2 : String) : Int :=
  compareNats (Str2Int s1) (Str2Int s2)
-- </vc-definitions>

-- <vc-theorems>
theorem Compare_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  (Str2Int s1 < Str2Int s2 → Compare s1 s2 = (-1 : Int)) ∧
  (Str2Int s1 = Str2Int s2 → Compare s1 s2 = 0) ∧
  (Str2Int s1 > Str2Int s2 → Compare s1 s2 = 1) := by
  constructor
  · intro h
    unfold Compare compareNats
    simp [h]
  · constructor
    · intro h
      unfold Compare compareNats
      simp [h]
    · intro h
      unfold Compare compareNats
      have not_lt : ¬(Str2Int s1 < Str2Int s2) := Nat.not_lt.mpr (Nat.le_of_lt h)
      have not_eq : ¬(Str2Int s1 = Str2Int s2) := Nat.ne_of_gt h
      simp [not_lt, not_eq]
-- </vc-theorems>

end BignumLean
