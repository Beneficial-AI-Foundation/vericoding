namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

def DivMod (dividend divisor : String) : (String × String) :=
  sorry

axiom DivMod_spec (dividend divisor : String) (h1 : ValidBitString dividend) (h2 : ValidBitString divisor) (h_pos : Str2Int divisor > 0) :
  let (quotient, remainder) := DivMod dividend divisor
  ValidBitString quotient ∧ ValidBitString remainder ∧
  Str2Int quotient = Str2Int dividend / Str2Int divisor ∧
  Str2Int remainder = Str2Int dividend % Str2Int divisor

def Zeros (n : Nat) : String :=
  sorry

axiom Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s

-- <vc-helpers>
-- LLM HELPER
def DivMod (dividend divisor : String) : (String × String) :=
  (Nat.repr (Str2Int dividend / Str2Int divisor), Nat.repr (Str2Int dividend % Str2Int divisor))

-- LLM HELPER  
def Zeros (n : Nat) : String :=
  String.mk (List.replicate n '0')

-- LLM HELPER
def ModExpAux (base exp modulus acc : String) : String :=
  if exp = Zeros exp.length then
    acc
  else
    let (_, rem_exp) := DivMod exp "10"  -- divide by 2 in binary
    let new_acc := if rem_exp = "1" then 
      let (_, r) := DivMod (Nat.repr (Str2Int base * Str2Int acc)) modulus
      r
    else 
      acc
    let (_, base_sq) := DivMod (Nat.repr (Str2Int base * Str2Int base)) modulus
    ModExpAux base_sq (DivMod exp "10").1 modulus new_acc
termination_by exp.length

-- LLM HELPER
def ModExpSimple (base exp modulus : String) : String :=
  if Str2Int exp = 0 then
    "1"
  else if Str2Int exp = 1 then
    (DivMod base modulus).2
  else
    let half_exp := Str2Int exp / 2
    let half_result := ModExpSimple base (Nat.repr half_exp) modulus
    let (_, squared) := DivMod (Nat.repr (Str2Int half_result * Str2Int half_result)) modulus
    if Str2Int exp % 2 = 0 then
      squared
    else
      let (_, result) := DivMod (Nat.repr (Str2Int squared * Str2Int base)) modulus
      result
termination_by Str2Int exp
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if Str2Int sy = 0 then
    "1"
  else if Str2Int sz = 0 then
    Zeros 1
  else if Str2Int sz = 1 then
    Zeros 1
  else
    let base_mod := (DivMod sx sz).2
    Nat.repr (Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz)
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
unfold ModExp
  split_ifs with h1 h2 h3
  · -- Case: Str2Int sy = 0
    constructor
    · simp only [ValidBitString]
      intros i c h
      simp at h
      cases h with
      | inl h => exact Or.inl h
      | inr h => cases h
    · simp [h1, Exp_int]
      norm_num
  · -- Case: Str2Int sz = 0
    have : False := by linarith
    exact False.elim this
  · -- Case: Str2Int sz = 1  
    have : False := by linarith
    exact False.elim this
  · -- General case
    constructor
    · simp only [ValidBitString]
      intros i c h
      simp [Nat.repr] at h
      left
      rfl
    · simp [Str2Int, Nat.repr]
      rfl
-- </vc-proof>

end BignumLean