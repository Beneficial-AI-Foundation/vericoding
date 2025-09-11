namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
-- (No additional helper lemmas required for this proof.)
-- </vc-helpers>

-- <vc-spec>
def CompareUnequal (s1 s2 : String) : Int :=
-- </vc-spec>
-- <vc-code>
def CompareUnequal (s1 s2 : String) : Int
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
dsimp [CompareUnequal]
constructor
· intro hlt
  simp [hlt]
· constructor
  · intro heq
    by_cases hlt' : Str2Int s1 < Str2Int s2
    · -- hlt' and heq contradict
      have : Str2Int s2 < Str2Int s2 := by rwa [heq] at hlt'
      exact absurd this (Nat.lt_irrefl (Str2Int s2))
    · simp [heq, hlt']
  · intro hgt
    by_cases hlt' : Str2Int s1 < Str2Int s2
    · -- hlt' and hgt contradict
      have h2 : Str2Int s2 < Str2Int s1 := hgt
      exact absurd h2 (Nat.lt_asymm hlt')
    · by_cases heq : Str2Int s1 = Str2Int s2
      · -- heq and hgt contradict
        have : Str2Int s1 < Str2Int s1 := by rwa [heq.symm] at hgt
        exact absurd this (Nat.lt_irrefl (Str2Int s1))
      · simp [hlt', heq]
-- </vc-proof>

end BignumLean