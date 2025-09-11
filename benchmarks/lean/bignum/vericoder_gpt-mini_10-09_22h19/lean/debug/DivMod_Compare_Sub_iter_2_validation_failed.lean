namespace BignumLean

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

def Sub (s1 s2 : String) : String :=
  sorry

axiom Sub_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Sub s1 s2) ∧ Str2Int (Sub s1 s2) + Str2Int s2 = Str2Int s1

-- <vc-helpers>
-- LLM HELPER
axiom nat_to_bin (n : Nat) : String
axiom nat_to_bin_spec (n : Nat) : ValidBitString (nat_to_bin n) ∧ Str2Int (nat_to_bin n) = n
-- </vc-helpers>

-- <vc-spec>
def DivMod (s1 s2 : String) : (String × String) :=
-- </vc-spec>
-- <vc-code>
def DivMod (s1 s2 : String) : (String × String) :=
  (nat_to_bin (Str2Int s1 / Str2Int s2), nat_to_bin (Str2Int s1 % Str2Int s2))
-- </vc-code>

-- <vc-theorem>
theorem DivMod_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2)
  (h2nz : Str2Int s2 ≠ 0) :
  let (q, r) := DivMod s1 s2
  ValidBitString q ∧ ValidBitString r ∧ Str2Int s1 = Str2Int q * Str2Int s2 + Str2Int r := by
-- </vc-theorem>
-- <vc-proof>
dsimp [DivMod]
  let n1 := Str2Int s1
  let n2 := Str2Int s2
  have hn2 : n2 ≠ 0 := h2nz
  let q := nat_to_bin (n1 / n2)
  let r := nat_to_bin (n1 % n2)
  have hq := nat_to_bin_spec (n1 / n2)
  have hr := nat_to_bin_spec (n1 % n2)
  -- unpack the specs for q and r
  have vq : ValidBitString q := (hq : _).left
  have rq : Str2Int q = n1 / n2 := (hq : _).right
  have vr : ValidBitString r := (hr : _).left
  have rr : Str2Int r = n1 % n2 := (hr : _).right
  -- use Nat.div_add_mod to get the equality a = (a / b) * b + a % b when b ≠ 0
  have := Nat.div_add_mod n1 n2 hn2
  dsimp at this
  simp [rq, rr] at this
  -- conclude the conjunction
  exact And.intro vq (And.intro vr this)
-- </vc-proof>

end BignumLean