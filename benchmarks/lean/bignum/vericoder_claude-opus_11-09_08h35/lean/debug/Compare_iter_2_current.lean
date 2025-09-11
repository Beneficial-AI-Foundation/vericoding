namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- No additional helpers needed
-- </vc-helpers>

-- <vc-spec>
def Compare (s1 s2 : String) : Int :=
-- </vc-spec>
-- <vc-code>
if Str2Int s1 < Str2Int s2 then (-1 : Int)
  else if Str2Int s1 = Str2Int s2 then 0
  else 1
-- </vc-code>

-- <vc-theorem>
theorem Compare_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  (Str2Int s1 < Str2Int s2 → Compare s1 s2 = (-1 : Int)) ∧
  (Str2Int s1 = Str2Int s2 → Compare s1 s2 = 0) ∧
  (Str2Int s1 > Str2Int s2 → Compare s1 s2 = 1) := by
-- </vc-theorem>
-- <vc-proof>
constructor
intro h
simp [Compare]
simp [h]
constructor
intro h
simp [Compare]
simp [h]
have : ¬(Str2Int s1 < Str2Int s2) := by
  rw [h]
  exact Nat.lt_irrefl (Str2Int s2)
simp [this]
intro h
simp [Compare]
have h1 : ¬(Str2Int s1 < Str2Int s2) := by
  exact Nat.not_lt.mpr (Nat.le_of_lt h)
simp [h1]
have h2 : ¬(Str2Int s1 = Str2Int s2) := by
  intro heq
  rw [heq] at h
  exact Nat.lt_irrefl (Str2Int s2) h
simp [h2]
-- </vc-proof>

end BignumLean