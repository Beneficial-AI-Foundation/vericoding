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
def CompareUnequal (s1 s2 : String) : Int :=
  if Str2Int s1 < Str2Int s2 then (-1 : Int)
  else if Str2Int s1 = Str2Int s2 then 0
  else 1
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
  -- first branch: if the Nat comparison is true, the if reduces to -1
  rw [if_pos hlt]
  rfl
· constructor
  · intro heq
    -- equality rules out the < case
    by_cases hlt : Str2Int s1 < Str2Int s2
    · have : Str2Int s2 < Str2Int s2 := by rwa [heq] at hlt
      exact absurd this (Nat.lt_irrefl _)
    · -- now the first if is false, the second if is true by heq
      rw [if_neg hlt, if_pos heq]
      rfl
  · intro hgt
    -- greater-than means the < case cannot hold; handle contradictions and the remaining else branch
    by_cases hlt : Str2Int s1 < Str2Int s2
    · -- hlt and hgt contradict by asymmetry
      have h2 : Str2Int s2 < Str2Int s1 := hgt
      exact absurd h2 (Nat.lt_asymm hlt)
    · by_cases heq : Str2Int s1 = Str2Int s2
      · -- equality contradicts hgt
        have : Str2Int s1 < Str2Int s1 := by rwa [heq.symm] at hgt
        exact absurd this (Nat.lt_irrefl _)
      · -- both previous tests false, so final branch yields 1
        rw [if_neg hlt, if_neg heq]
        rfl
-- </vc-proof>

end BignumLean