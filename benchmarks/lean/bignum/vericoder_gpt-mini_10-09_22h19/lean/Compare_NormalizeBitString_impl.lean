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
-- LLM HELPER
-- No additional helpers needed for this file.
-- </vc-helpers>

-- <vc-spec>
def Compare (s1 s2 : String) : Int :=
-- </vc-spec>
-- <vc-code>
if h : Str2Int s1 < Str2Int s2 then (-1 : Int)
else if h2 : Str2Int s1 = Str2Int s2 then 0
else 1
-- </vc-code>

-- <vc-theorem>
theorem Compare_spec (s1 s2 : String) :
  (Str2Int s1 < Str2Int s2 → Compare s1 s2 = (-1 : Int)) ∧
  (Str2Int s1 = Str2Int s2 → Compare s1 s2 = 0) ∧
  (Str2Int s1 > Str2Int s2 → Compare s1 s2 = 1) := by
-- </vc-theorem>
-- <vc-proof>
dsimp [Compare]
constructor
· intro hlt
  simp [if_pos hlt]
· constructor
  · intro heq
    have hnot : ¬ Str2Int s1 < Str2Int s2 := by
      intro h
      rw [heq] at h
      exact Nat.lt_irrefl _ h
    simp [if_neg hnot, if_pos heq]
  · intro hgt
    have hnot : ¬ Str2Int s1 < Str2Int s2 := fun h => Nat.lt_asymm h hgt
    have hneq : ¬ Str2Int s1 = Str2Int s2 := fun heq => by
      rw [heq] at hgt
      exact Nat.lt_irrefl _ hgt
    simp [if_neg hnot, if_neg hneq]
-- </vc-proof>

end BignumLean