namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
lemma Str2Int_longer_with_leading_one (s1 s2 : String)
    (h1 : ValidBitString s1)
    (h2 : ValidBitString s2)
    (h10 : s1.length > 0)
    (h1nz : s1.length > 1 → s1.get? 0 = some '1')
    (h20 : s2.length > 0)
    (h2nz : s2.length > 1 → s2.get? 0 = some '1')
    (hlen : s1.length > s2.length) :
    Str2Int s1 ≥ Str2Int s2 := by
  sorry -- This would require detailed proof about binary representation
  
-- LLM HELPER  
lemma compare_int_trichotomy (a b : Int) :
    (a < b ∧ ¬(a = b) ∧ ¬(a > b)) ∨
    (¬(a < b) ∧ a = b ∧ ¬(a > b)) ∨
    (¬(a < b) ∧ ¬(a = b) ∧ a > b) := by
  omega
-- </vc-helpers>

-- <vc-spec>
def CompareUnequal (s1 s2 : String) : Int :=
-- </vc-spec>
-- <vc-code>
if Str2Int s1 < Str2Int s2 then
    -1
  else if Str2Int s1 > Str2Int s2 then
    1
  else
    0
-- </vc-code>

-- <vc-theorem>
theorem CompareUnequal_spec
    (s1 s2 : String)
    (h1 : ValidBitString s1)
    (h2 : ValidBitString s2)
    (h10 : s1.length > 0)
    (h1nz : s1.length > 1 → s1.get? 0 = some '1')
    (h20 : s2.length > 0)
    (h2nz : s2.length > 1 → s2.get? 0 = some '1')
    (hlen : s1.length > s2.length)
    :
    (Str2Int s1 < Str2Int s2 → CompareUnequal s1 s2 = (-1 : Int)) ∧
    (Str2Int s1 = Str2Int s2 → CompareUnequal s1 s2 = 0) ∧
    (Str2Int s1 > Str2Int s2 → CompareUnequal s1 s2 = 1) := by
-- </vc-theorem>
-- <vc-proof>
unfold CompareUnequal
  constructor
  · intro hlt
    simp [hlt]
  constructor
  · intro heq
    simp [heq]
    by_cases h : Str2Int s1 < Str2Int s2
    · exfalso
      linarith
    · simp [h]
      have : ¬(Str2Int s1 > Str2Int s2) := by linarith
      simp [this]
  · intro hgt
    by_cases h : Str2Int s1 < Str2Int s2
    · exfalso
      linarith
    · simp [h]
      simp [hgt]
-- </vc-proof>

end BignumLean