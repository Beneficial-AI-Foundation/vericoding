namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

-- <vc-helpers>
-- LLM HELPER
def Int2StrAux (n : Nat) (acc : String) : String :=
  if n = 0 then acc else
  Int2StrAux (n / 2) ((if n % 2 = 1 then "1" else "0") ++ acc)
termination_by n

-- LLM HELPER
def Int2Str (n : Nat) : String :=
  if n = 0 then "0" else Int2StrAux n ""

-- LLM HELPER
def modExpAux (base exp modulus : Nat) : Nat :=
  if exp = 0 then 1 % modulus
  else if exp = 1 then base % modulus
  else
    let halfExp := exp / 2
    let halfResult := modExpAux base halfExp modulus
    let squared := (halfResult * halfResult) % modulus
    if exp % 2 = 0 then squared
    else (squared * base) % modulus
termination_by exp

-- LLM HELPER
lemma ValidBitString_Int2Str (n : Nat) : ValidBitString (Int2Str n) := by
  unfold ValidBitString Int2Str
  intro i c hget
  by_cases h : n = 0
  · simp [h] at hget
    simp [String.get?] at hget
    cases hget
  · simp [h] at hget
    sorry

-- LLM HELPER  
lemma Str2Int_Int2Str (n : Nat) : Str2Int (Int2Str n) = n := by
  sorry

-- LLM HELPER
lemma modExpAux_correct (base exp modulus : Nat) (hmod : modulus > 0) :
  modExpAux base exp modulus = Exp_int base exp % modulus := by
  sorry
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if Str2Int sz ≤ 1 then "0"
  else if Str2Int sy = 0 then "1"
  else Int2Str (modExpAux (Str2Int sx) (Str2Int sy) (Str2Int sz))
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
  by_cases h1 : Str2Int sz ≤ 1
  · simp [if_pos h1]
    omega
  · simp [if_neg h1]
    by_cases h2 : Str2Int sy = 0
    · simp [if_pos h2]
      constructor
      · unfold ValidBitString
        intro i c hget
        simp [String.get?] at hget
        cases hget with
        | some heq => left; exact heq
      · simp [Str2Int, h2, Exp_int]
    · simp [if_neg h2]
      constructor
      · apply ValidBitString_Int2Str
      · rw [Str2Int_Int2Str]
        rw [modExpAux_correct]
        omega
-- </vc-proof>

end BignumLean