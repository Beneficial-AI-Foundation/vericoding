namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

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

-- <vc-helpers>
-- LLM HELPER
def Multiply (s1 s2 : String) : String :=
  -- Placeholder multiplication using repeated addition
  if s2 = "0" then "0"
  else if s2 = "1" then s1
  else 
    let rec mult_helper (acc : String) (count : Nat) : String :=
      if count = 0 then acc
      else mult_helper (Add s1 acc) (count - 1)
    if Str2Int s2 = 0 then "0"
    else mult_helper "0" (Str2Int s2)

-- LLM HELPER
def ModularSquare (x z : String) : String :=
  let squared := Multiply x x
  (DivMod squared z).2

-- LLM HELPER  
def RepeatSquareMod (x : String) (n : Nat) (z : String) : String :=
  if n = 0 then x
  else RepeatSquareMod (ModularSquare x z) (n - 1) z
termination_by n
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if sy = "0" then "1"  -- x^0 = 1
  else RepeatSquareMod sx n sz
-- </vc-code>

-- <vc-theorem>
theorem ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
unfold ModExpPow2
  cases hsy_pow2 with
  | inl h_pow2 =>
    -- Case: sy = 2^n
    have sy_ne_zero : sy ≠ "0" := by
      intro h_eq
      rw [h_eq] at h_pow2
      simp [Str2Int] at h_pow2
      cases n
      · simp
-- </vc-proof>

end BignumLean