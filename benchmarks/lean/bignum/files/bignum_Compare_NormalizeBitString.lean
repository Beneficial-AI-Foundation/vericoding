-- <vc-preamble>
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
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Compare (s1 s2 : String) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Compare_spec (s1 s2 : String) :
  (Str2Int s1 < Str2Int s2 → Compare s1 s2 = (-1 : Int)) ∧
  (Str2Int s1 = Str2Int s2 → Compare s1 s2 = 0) ∧
  (Str2Int s1 > Str2Int s2 → Compare s1 s2 = 1) := by
  sorry
-- </vc-theorems>