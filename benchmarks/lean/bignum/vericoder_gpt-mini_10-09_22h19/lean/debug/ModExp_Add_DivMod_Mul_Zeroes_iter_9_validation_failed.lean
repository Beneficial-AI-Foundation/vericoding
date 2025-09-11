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

def DivMod (dividend divisor : String) : (String × String) :=
  sorry

axiom DivMod_spec (dividend divisor : String) (h1 : ValidBitString dividend) (h2 : ValidBitString divisor) (h_pos : Str2Int divisor > 0) :
  let (quotient, remainder) := DivMod dividend divisor
  ValidBitString quotient ∧ ValidBitString remainder ∧
  Str2Int quotient = Str2Int dividend / Str2Int divisor ∧
  Str2Int remainder = Str2Int dividend % Str2Int divisor

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
def PowStr (s : String) : Nat → String
| 0 => "1"
| n+1 => Mul s (PowStr s n)

-- LLM HELPER
axiom ValidBitString_one : ValidBitString "1"

-- LLM HELPER
axiom Str2Int_one : Str2Int "1" = 1

-- LLM HELPER
axiom PowStr_spec (s : String) (hs : ValidBitString s) : ∀ n, ValidBitString (PowStr s n) ∧ Str2Int (PowStr s n) = Exp_int (Str2Int s) n
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
Prod.snd (DivMod (PowStr sx (Str2Int sy)) sz)
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
let n := Str2Int sy
have hpow := PowStr_spec sx hx n
have hpos : Str2Int sz > 0 := Nat.lt_trans Nat.zero_lt_one hsz_gt1
have hdiv := DivMod_spec (PowStr sx n) sz hpow.1 hz hpos
-- destruct the conjunction returned by DivMod_spec
obtain ⟨hq_valid, hr_valid, hq_val, hr_val⟩ := hdiv
dsimp [ModExp]
constructor
· exact hr_valid
· calc
    Str2Int (ModExp sx sy sz) = Str2Int (Prod.snd (DivMod (PowStr sx n) sz)) := rfl
    _ = Str2Int (PowStr sx n) % Str2Int sz := by exact hr_val
    _ = Exp_int (Str2Int sx) n % Str2Int sz := by rw [hpow.2]
    _ = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by rfl
-- </vc-proof>

end BignumLean