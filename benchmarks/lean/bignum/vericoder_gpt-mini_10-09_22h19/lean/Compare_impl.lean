namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- No helpers needed for this development.
-- LLM HELPER: None added.
-- </vc-helpers>

-- <vc-spec>
def Compare (s1 s2 : String) : Int :=
-- </vc-spec>
-- <vc-code>
let n1 := Str2Int s1
let n2 := Str2Int s2
if h : n1 < n2 then (-1 : Int) else
  if h2 : n1 = n2 then 0 else 1
-- </vc-code>

-- <vc-theorem>
theorem Compare_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  (Str2Int s1 < Str2Int s2 → Compare s1 s2 = (-1 : Int)) ∧
  (Str2Int s1 = Str2Int s2 → Compare s1 s2 = 0) ∧
  (Str2Int s1 > Str2Int s2 → Compare s1 s2 = 1) := by
  dsimp [Compare]
  constructor
  · intro hlt
    simp [if_pos hlt]
  · constructor
    · intro heq
      have hlt_false : ¬ (Str2Int s1 < Str2Int s2) := by
        intro h; rw [heq] at h; exact Nat.lt_irrefl (Str2Int s2) h
      simp [if_neg hlt_false, if_pos heq]
    · intro hgt
      have hlt_false : ¬ (Str2Int s1 < Str2Int s2) := by
        intro hlt; have trans := Nat.lt_trans hgt hlt; exact Nat.lt_irrefl (Str2Int s2) trans
      have heq_false : ¬ (Str2Int s1 = Str2Int s2) := by
        intro heq; rw [heq] at hgt; exact Nat.lt_irrefl (Str2Int s2) hgt
      simp [if_neg hlt_false, if_neg heq_false]
-- </vc-theorem>
-- <vc-proof>
-- Proof provided inline in the theorem above.
-- </vc-proof>

end BignumLean