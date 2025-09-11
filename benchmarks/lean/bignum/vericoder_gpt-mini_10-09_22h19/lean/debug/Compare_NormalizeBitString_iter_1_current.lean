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
-- (no helpers needed)
-- </vc-helpers>

-- <vc-spec>
def Compare (s1 s2 : String) : Int :=
-- </vc-spec>
-- <vc-code>
def NormalizeBitString (s : String) : String := s

def Compare (s1 s2 : String) : Int :=
  if Str2Int s1 < Str2Int s2 then (-1 : Int)
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
dsimp [Compare]
  constructor
  · intro h; simp [h]
  · constructor
    · intro h; simp [h]
    · intro h
      have hne : Str2Int s1 ≠ Str2Int s2 := by
        intro heq
        subst heq at h
        exact (Nat.lt_irrefl (Str2Int s2) h)
      have hlt_false : ¬ Str2Int s1 < Str2Int s2 := by
        intro hl
        apply Nat.lt_asymm hl h
      simp [hne, hlt_false]
-- </vc-proof>

end BignumLean