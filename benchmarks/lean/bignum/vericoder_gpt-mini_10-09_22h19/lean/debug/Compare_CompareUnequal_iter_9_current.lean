namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
theorem nat_gt_to_lt {a b : Nat} (h : a > b) : b < a := Nat.gt_iff_lt.mp h
-- </vc-helpers>

-- <vc-spec>
def CompareUnequal (s1 s2 : String) : Int :=
-- </vc-spec>
-- <vc-code>
def CompareUnequal (s1 s2 : String) : Int :=
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
unfold CompareUnequal
split_ifs with hlt heq
-- Case 1: Str2Int s1 < Str2Int s2
constructor
· intro h; rfl
· constructor
  · intro he
    -- equality contradicts the strict inequality hlt
    rw [he] at hlt
    exact Nat.lt_irrefl _ hlt
  · intro hgt
    -- hgt : Str2Int s1 > Str2Int s2, convert to lt and get asymmetry
    have h2 : Str2Int s2 < Str2Int s1 := nat_gt_to_lt hgt
    exact Nat.lt_asymm hlt h2

-- Case 2: ¬(Str2Int s1 < Str2Int s2) and Str2Int s1 = Str2Int s2
constructor
· intro h; exact hlt h
· constructor
  · intro he; rfl
  · intro hgt
    -- hgt contradicts equality
    rw [heq] at hgt
    have hlt' : Str2Int s1 < Str2Int s1 := nat_gt_to_lt hgt
    exact Nat.lt_irrefl _ hlt'

-- Case 3: ¬(Str2Int s1 < Str2Int s2) and ¬(Str2Int s1 = Str2Int s2)
constructor
· intro h; exact hlt h
· constructor
  · intro he; exact heq he
  · intro hgt; rfl
-- </vc-proof>

end BignumLean