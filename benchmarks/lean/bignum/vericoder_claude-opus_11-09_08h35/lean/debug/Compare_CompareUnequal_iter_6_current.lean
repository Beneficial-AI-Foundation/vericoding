namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
lemma str2int_nonneg (s : String) : 0 ≤ Str2Int s := by
  unfold Str2Int
  induction s.data with
  | nil => simp [List.foldl]
  | cons h t ih =>
    simp [List.foldl]
    have : 0 ≤ t.foldl (fun acc ch => 2 * acc + if ch = '1' then 1 else 0) 0 := ih
    by_cases hc : h = '1' <;> simp [hc] <;> omega
-- </vc-helpers>

-- <vc-spec>
def CompareUnequal (s1 s2 : String) : Int :=
-- </vc-spec>
-- <vc-code>
if Str2Int s1 < Str2Int s2 then -1
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
unfold CompareUnequal
  constructor
  · intro h_lt
    simp [h_lt]
  constructor
  · intro h_eq
    simp [h_eq]
    have : ¬(Str2Int s1 < Str2Int s2) := by omega
    simp [this]
  · intro h_gt
    have h_not_lt : ¬(Str2Int s1 < Str2Int s2) := by omega
    have h_not_eq : ¬(Str2Int s1 = Str2Int s2) := by omega
    simp [h_not_lt, h_not_eq]
-- </vc-proof>

end BignumLean