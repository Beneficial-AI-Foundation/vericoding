import Mathlib
-- <vc-preamble>

namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: no additional helpers required for this file
-- </vc-helpers>


-- <vc-definitions>
def CompareUnequal (s1 s2 : String) : Int :=
  if Str2Int s1 < Str2Int s2 then (-1 : Int) else if Str2Int s1 = Str2Int s2 then (0 : Int) else (1 : Int)
-- </vc-definitions>

-- <vc-theorems>
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
  constructor
  · intro hlt
    unfold CompareUnequal
    simp [hlt]
  · constructor
    · intro heq
      unfold CompareUnequal
      have hlt_false : ¬ Str2Int s1 < Str2Int s2 := by
        simpa [heq] using (lt_irrefl (Str2Int s1))
      simp [hlt_false, heq]
    · intro hgt
      unfold CompareUnequal
      have hlt_false : ¬ Str2Int s1 < Str2Int s2 := by
        intro hlt
        have hgt' : Str2Int s2 < Str2Int s1 := by
          simpa [gt_iff_lt] using hgt
        exact lt_asymm hlt hgt'
      have hne : Str2Int s1 ≠ Str2Int s2 := ne_of_gt hgt
      simp [hlt_false, hne]
-- </vc-theorems>

end BignumLean
