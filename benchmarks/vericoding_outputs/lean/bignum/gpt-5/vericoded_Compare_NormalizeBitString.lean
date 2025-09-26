import Mathlib
-- <vc-preamble>

namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0


def NormalizeBitString (s : String) : String :=
  sorry

axiom NormalizeBitString_spec (s : String) (h : ValidBitString s) :
  let t := NormalizeBitString s
  ValidBitString t ∧
  t.length > 0 ∧
  (t.length > 1 → t.get? 0 = some '1') ∧
  Str2Int s = Str2Int t
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def signumNat (a b : Nat) : Int :=
  if a < b then (-1 : Int) else if a = b then 0 else 1
-- </vc-helpers>


-- <vc-definitions>
def Compare (s1 s2 : String) : Int :=
  if Str2Int s1 < Str2Int s2 then (-1 : Int)
else if Str2Int s1 = Str2Int s2 then 0
else 1
-- </vc-definitions>


-- <vc-theorems>
theorem Compare_spec (s1 s2 : String) :
  (Str2Int s1 < Str2Int s2 → Compare s1 s2 = (-1 : Int)) ∧
  (Str2Int s1 = Str2Int s2 → Compare s1 s2 = 0) ∧
  (Str2Int s1 > Str2Int s2 → Compare s1 s2 = 1) := by
  constructor
  · intro hlt
    simp [Compare, hlt]
  · constructor
    · intro heq
      have hnotlt : ¬ Str2Int s1 < Str2Int s2 := by
        simpa [heq] using (Nat.lt_irrefl (Str2Int s2))
      simp [Compare, hnotlt, heq]
    · intro hgt
      have hnotlt : ¬ Str2Int s1 < Str2Int s2 := by
        have hba : Str2Int s2 < Str2Int s1 := hgt
        exact lt_asymm hba
      have hne : Str2Int s1 ≠ Str2Int s2 := ne_of_gt hgt
      simp [Compare, hnotlt, hne]
-- </vc-theorems>

end BignumLean
