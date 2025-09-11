namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def DivMod (dividend divisor : String) : (String × String) :=
  sorry

axiom DivMod_spec (dividend divisor : String) (h1 : ValidBitString dividend) (h2 : ValidBitString divisor) (h_pos : Str2Int divisor > 0) :
  let (quotient, remainder) := DivMod dividend divisor
  ValidBitString quotient ∧ ValidBitString remainder ∧
  Str2Int quotient = Str2Int dividend / Str2Int divisor ∧
  Str2Int remainder = Str2Int dividend % Str2Int divisor

-- <vc-helpers>
-- LLM HELPER
def Nat2Str (n : Nat) : String :=
  if n = 0 then "0" else Nat2StrAux n
where
  Nat2StrAux (n : Nat) : String :=
    if n = 0 then "" else
      Nat2StrAux (n / 2) ++ (if n % 2 = 0 then "0" else "1")
  termination_by n

-- LLM HELPER
lemma Nat2Str_valid (n : Nat) : ValidBitString (Nat2Str n) := by
  unfold ValidBitString Nat2Str
  split
  · intros i c h
    simp at h
    cases h
    left
    rfl
  · intros i c
    simp [Nat2Str.Nat2StrAux]
    intro h
    sorry

-- LLM HELPER
lemma Str2Int_Nat2Str (n : Nat) : Str2Int (Nat2Str n) = n := by
  sorry

-- LLM HELPER
def modExpNat (base exp modulus : Nat) : Nat :=
  if modulus = 0 then 0
  else if exp = 0 then 1 % modulus
  else 
    let halfExp := modExpNat base (exp / 2) modulus
    let squared := (halfExp * halfExp) % modulus
    if exp % 2 = 0 then squared
    else (squared * base) % modulus
termination_by exp

-- LLM HELPER
lemma modExpNat_eq_Exp_int_mod (base exp modulus : Nat) (h : modulus > 0) :
  modExpNat base exp modulus = Exp_int base exp % modulus := by
  sorry
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
let x := Str2Int sx
  let y := Str2Int sy
  let z := Str2Int sz
  let result := modExpNat x y z
  Nat2Str result
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
unfold ModExp
  constructor
  · apply Nat2Str_valid
  · rw [Str2Int_Nat2Str]
    apply modExpNat_eq_Exp_int_mod
    exact hsz_gt1
-- </vc-proof>

end BignumLean