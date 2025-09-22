-- <vc-preamble>
def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Compare (s1 s2 : String) : Int :=
  sorry

axiom Compare_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  (Str2Int s1 < Str2Int s2 → Compare s1 s2 = (-1 : Int)) ∧
  (Str2Int s1 = Str2Int s2 → Compare s1 s2 = 0) ∧
  (Str2Int s1 > Str2Int s2 → Compare s1 s2 = 1)

def Sub_ (s1 s2 : String) : String :=
  sorry

axiom Sub_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Sub_ s1 s2) ∧ Str2Int (Sub_ s1 s2) + Str2Int s2 = Str2Int s1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def DivMod (s1 s2 : String) : (String × String) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem DivMod_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2)
  (h2nz : Str2Int s2 ≠ 0) :
  let (q, r) := DivMod s1 s2
  ValidBitString q ∧ ValidBitString r ∧ Str2Int s1 = Str2Int q * Str2Int s2 + Str2Int r := by
  sorry
-- </vc-theorems>