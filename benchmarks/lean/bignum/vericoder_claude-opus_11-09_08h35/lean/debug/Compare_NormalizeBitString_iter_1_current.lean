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

-- <vc-helpers>
-- No additional helpers needed
-- </vc-helpers>

-- <vc-spec>
def Compare (s1 s2 : String) : Int :=
-- </vc-spec>
-- <vc-code>
if Str2Int s1 < Str2Int s2 then -1
  else if Str2Int s1 = Str2Int s2 then 0
  else 1
-- </vc-code>

-- <vc-theorem>
theorem Compare_spec (s1 s2 : String) :
  (Str2Int s1 < Str2Int s2 → Compare s1 s2 = (-1 : Int)) ∧
  (Str2Int s1 = Str2Int s2 → Compare s1 s2 = 0) ∧
  (Str2Int s1 > Str2Int s2 → Compare s1 s2 = 1) := by
-- </vc-theorem>
-- <vc-proof>
constructor
  · intro h
    unfold Compare
    simp [if_pos h]
  constructor
  · intro h
    unfold Compare
    simp [if_neg (Nat.not_lt.mpr (Nat.le_of_eq h)), if_pos h]
  · intro h
    unfold Compare
    simp [if_neg (Nat.not_lt.mpr (Nat.le_of_lt h)), if_neg (Ne.symm (Nat.ne_of_gt h))]
-- </vc-proof>

end BignumLean