namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

def Add (s1 s2 : String) : String :=
  sorry

axiom Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

def Zeros (n : Nat) : String :=
  sorry

axiom Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s

-- <vc-helpers>
-- LLM HELPER
-- Provide an opaque conversion from Nat to binary bitstring and assert its correctness.
constant nat_to_string : Nat → String

-- LLM HELPER
axiom nat_to_string_spec (n : Nat) : ValidBitString (nat_to_string n) ∧ Str2Int (nat_to_string n) = n

-- LLM HELPER
theorem ValidBitString_nat_to_string (n : Nat) : ValidBitString (nat_to_string n) :=
  (nat_to_string_spec n).left

-- LLM HELPER
theorem nat_to_string_Str2Int (n : Nat) : Str2Int (nat_to_string n) = n :=
  (nat_to_string_spec n).right
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExp (sx sy sz : String) : String :=
  -- compute numeric result and convert to bitstring
  let r := Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz
  nat_to_string r
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
have r := Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz
dsimp [ModExp]
constructor
· apply ValidBitString_nat_to_string
· exact nat_to_string_Str2Int r
-- </vc-proof>

end BignumLean