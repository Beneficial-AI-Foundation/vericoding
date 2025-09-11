namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
-- (no extra helpers needed)
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
  -- decide p = true ↔ p, use .mpr to go from Prop proof to Bool-equality
  have dlt := (decide_eq_true (Str2Int s1 < Str2Int s2)).mpr hlt
  simp [dlt]
  rfl
· constructor
  · intro heq
    -- if equal then the first comparison is false
    have ndlt : decide (Str2Int s1 < Str2Int s2) = false :=
      (decide_eq_false (Str2Int s1 < Str2Int s2)).mpr (by
        intro H; rw [heq] at H; exact Nat.lt_irrefl _ H)
    -- and decide equality is true
    have deq := (decide_eq_true (Str2Int s1 = Str2Int s2)).mpr heq
    simp [ndlt, deq]
    rfl
  · intro hgt
    -- if greater, the less-than check is false
    have ndlt : decide (Str2Int s1 < Str2Int s2) = false :=
      (decide_eq_false (Str2Int s1 < Str2Int s2)).mpr (by
        intro H; exact Nat.lt_asymm H hgt)
    -- and equality check is false
    have ndeq : decide (Str2Int s1 = Str2Int s2) = false :=
      (decide_eq_false (Str2Int s1 = Str2Int s2)).mpr (by
        intro H; rw [H] at hgt; exact Nat.lt_irrefl _ hgt)
    simp [ndlt, ndeq]
    rfl
-- </vc-proof>

end BignumLean