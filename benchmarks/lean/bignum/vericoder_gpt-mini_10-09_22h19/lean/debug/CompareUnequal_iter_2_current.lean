namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- (no helpers needed)
-- </vc-helpers>

-- <vc-spec>
def CompareUnequal (s1 s2 : String) : Int :=
-- </vc-spec>
-- <vc-code>
if decide (Str2Int s1 < Str2Int s2) then (-1 : Int)
else if decide (Str2Int s1 = Str2Int s2) then 0 else 1
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
  have dlt := decide_eq_true.2 hlt
  simp [dlt]
  rfl
· constructor
  · intro heq
    have ndlt : decide (Str2Int s1 < Str2Int s2) = false :=
      decide_eq_false.2 (by intro H; rw [heq] at H; exact Nat.lt_irrefl _ H)
    have deq := decide_eq_true.2 heq
    simp [ndlt, deq]
    rfl
  · intro hgt
    have ndlt : decide (Str2Int s1 < Str2Int s2) = false :=
      decide_eq_false.2 (by intro H; exact Nat.lt_asymm H (by exact hgt))
    have ndeq : decide (Str2Int s1 = Str2Int s2) = false :=
      decide_eq_false.2 (by intro H; rw [H] at hgt; exact Nat.lt_irrefl _ hgt)
    simp [ndlt, ndeq]
    rfl
-- </vc-proof>

end BignumLean