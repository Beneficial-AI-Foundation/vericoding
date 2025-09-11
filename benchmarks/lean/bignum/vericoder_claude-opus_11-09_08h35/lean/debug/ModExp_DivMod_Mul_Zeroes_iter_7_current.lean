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
def ModExpHelper (base exp modulus result : String) : String :=
  if exp = Zeros exp.length then
    result
  else
    let (exp_div2, exp_mod2) := DivMod exp "10"  -- divide by 2 in binary
    let new_result := if exp_mod2 = "1" then 
      (DivMod (Mul result base) modulus).2  -- (result * base) % modulus
    else 
      result
    let new_base := (DivMod (Mul base base) modulus).2  -- (base * base) % modulus
    ModExpHelper new_base exp_div2 modulus new_result
termination_by exp.length

-- LLM HELPER
lemma binary_two_repr : ValidBitString "10" ∧ Str2Int "10" = 2 := by
  constructor
  · intro i c h
    match i with
    | 0 => simp [String.get?] at h; simp [h]
    | 1 => simp [String.get?] at h; simp [h]
    | n+2 => simp [String.get?] at h
  · simp [Str2Int, String.data]

-- LLM HELPER  
lemma binary_one_repr : ValidBitString "1" ∧ Str2Int "1" = 1 := by
  constructor
  · intro i c h
    match i with
    | 0 => simp [String.get?] at h; simp [h]
    | n+1 => simp [String.get?] at h
  · simp [Str2Int, String.data]

-- LLM HELPER
lemma modexp_helper_valid (base exp modulus result : String) 
  (h_base : ValidBitString base) (h_exp : ValidBitString exp) 
  (h_mod : ValidBitString modulus) (h_result : ValidBitString result)
  (h_mod_gt1 : Str2Int modulus > 1) :
  ValidBitString (ModExpHelper base exp modulus result) := by
  termination_by exp.length
  by_cases h : exp = Zeros exp.length
  · simp [ModExpHelper, h]
    exact h_result
  · simp [ModExpHelper, h]
    have h_two := binary_two_repr
    have h_divmod := DivMod_spec exp "10" h_exp h_two.1 (by simp [h_two.2])
    obtain ⟨h_q_valid, h_r_valid, _, _⟩ := h_divmod
    by_cases h_odd : (DivMod exp "10").2 = "1"
    · simp [h_odd]
      have h_mul := Mul_spec result base h_result h_base
      have h_mod_res := DivMod_spec (Mul result base) modulus h_mul.1 h_mod h_mod_gt1
      have h_base2 := Mul_spec base base h_base h_base
      have h_mod_base := DivMod_spec (Mul base base) modulus h_base2.1 h_mod h_mod_gt1
      apply modexp_helper_valid
      · exact h_mod_base.2.1
      · exact h_q_valid
      · exact h_mod
      · exact h_mod_res.2.1
      · exact h_mod_gt1
    · simp [h_odd]
      have h_base2 := Mul_spec base base h_base h_base
      have h_mod_base := DivMod_spec (Mul base base) modulus h_base2.1 h_mod h_mod_gt1
      apply modexp_helper_valid
      · exact h_mod_base.2.1
      · exact h_q_valid
      · exact h_mod
      · exact h_result
      · exact h_mod_gt1
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
let base_mod := (DivMod sx sz).2  -- sx % sz
ModExpHelper base_mod sy sz "1"
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
simp [ModExp]
have h_divmod_base := DivMod_spec sx sz hx hz hsz_gt1
obtain ⟨_, h_base_valid, _, h_base_val⟩ := h_divmod_base
have h_one := binary_one_repr
constructor
· apply modexp_helper_valid
  · exact h_base_valid
  · exact hy
  · exact hz
  · exact h_one.1
  · exact hsz_gt1
· simp [h_base_val]
  rfl
-- </vc-proof>

end BignumLean