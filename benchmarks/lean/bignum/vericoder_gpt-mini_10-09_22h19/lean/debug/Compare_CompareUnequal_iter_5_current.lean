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
if Str2Int s1 < Str2Int s2 then (-1 : Int)
else if Str2Int s1 = Str2Int s2 then (0 : Int)
else (1 : Int)
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
  -- if the Nat comparison is true, the outer if reduces to -1
  rw [if_pos hlt]
  rfl
· constructor
  · intro heq
    -- equality rules out the < case
    have hnotlt : ¬ (Str2Int s1 < Str2Int s2) := by
      intro h
      rw [heq] at h
      exact absurd h (Nat.lt_irrefl _)
    rw [if_neg hnotlt, if_pos heq]
    rfl
  · intro hgt
    -- greater-than rules out both < and = cases
    have hnotlt : ¬ (Str2Int s1 < Str2Int s2) := by
      intro h
      have h2 : Str2Int s2 < Str2Int s1 := Nat.lt_of_gt hgt
      exact Nat.lt_asymm h h2
    have hnoteq : ¬ (Str2Int s1 = Str2Int s2) := by
      intro he
      have : Str2Int s1 < Str2Int s1 := by
        rw [he] at hgt
        exact Nat.lt_of_gt hgt
      exact absurd this (Nat.lt_irrefl _)
    rw [if_neg hnotlt, if_neg hnoteq]
    rfl
-- </vc-proof>

end BignumLean