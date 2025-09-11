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
  by_cases h : Str2Int s1 < Str2Int s2
  · simp [h]
  · contradiction
· constructor
  · intro heq
    by_cases h : Str2Int s1 < Str2Int s2
    · -- h and heq contradict
      rw [heq] at h
      exact Nat.lt_irrefl _ h
    · by_cases heq2 : Str2Int s1 = Str2Int s2
      · simp [heq2]
      · -- heq2 is ¬ (Str2Int s1 = Str2Int s2), contradicts heq
        contradiction
  · intro hgt
    by_cases h : Str2Int s1 < Str2Int s2
    · -- h and hgt contradict by asymmetry
      exact (Nat.lt_asymm h hgt)
    · by_cases heq2 : Str2Int s1 = Str2Int s2
      · -- equality contradicts hgt
        rw [heq2] at hgt
        exact Nat.lt_irrefl _ hgt
      · -- both ¬lt and ¬eq hold, so else branch yields 1
        simp [h, heq2]
-- </vc-proof>

end BignumLean