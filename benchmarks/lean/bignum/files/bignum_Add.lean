-- <vc-preamble>
def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Add_ (s1 s2 : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add_ s1 s2) ∧ Str2Int (Add_ s1 s2) = Str2Int s1 + Str2Int s2 := by
  sorry
-- </vc-theorems>