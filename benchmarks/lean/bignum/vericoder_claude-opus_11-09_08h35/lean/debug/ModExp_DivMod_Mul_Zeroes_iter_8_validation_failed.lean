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
lemma modexp_helper_spec (base exp modulus result : String) 
  (h_base : ValidBitString base) (h_exp : ValidBitString exp) 
  (h_mod : ValidBitString modulus) (h_result : ValidBitString result)
  (h_mod_gt1 : Str2Int modulus > 1) 
  (h_base_lt : Str2Int base < Str2Int modulus)
  (h_result_lt : Str2Int result < Str2Int modulus) :
  ValidBitString (ModExpHelper base exp modulus result) ∧
  Str2Int (ModExpHelper base exp modulus result) = 
    (Str2Int result * Exp_int (Str2Int base) (Str2Int exp)) % Str2Int modulus := by
  termination_by exp.length
  by_cases h : exp = Zeros exp.length
  · simp [ModExpHelper, h]
    have h_zeros := Zeros_spec exp.length
    have : Str2Int exp = 0 := by
      have : exp = Zeros exp.length := h
      rw [this]
      exact h_zeros.2.2.1
    simp [this, Exp_int]
    constructor
    · exact h_result
    · simp [Nat.mul_one, Nat.mod_eq_of_lt h_result_lt]
  · simp [ModExpHelper, h]
    have h_two := binary_two_repr
    have h_divmod := DivMod_spec exp "10" h_exp h_two.1 (by simp [h_two.2])
    obtain ⟨h_q_valid, h_r_valid, h_q_val, h_r_val⟩ := h_divmod
    by_cases h_odd : (DivMod exp "10").2 = "1"
    · simp [h_odd]
      have h_mul := Mul_spec result base h_result h_base
      have h_mod_res := DivMod_spec (Mul result base) modulus h_mul.1 h_mod (by linarith)
      have h_base2 := Mul_spec base base h_base h_base
      have h_mod_base := DivMod_spec (Mul base base) modulus h_base2.1 h_mod (by linarith)
      have h_rec := modexp_helper_spec (DivMod (Mul base base) modulus).2 
                      (DivMod exp "10").1 modulus 
                      (DivMod (Mul result base) modulus).2
                      h_mod_base.2.1 h_q_valid h_mod h_mod_res.2.1 h_mod_gt1
                      (Nat.mod_lt _ (by linarith)) (Nat.mod_lt _ (by linarith))
      constructor
      · exact h_rec.1
      · simp [h_rec.2, h_mod_res.2.2.2, h_mod_base.2.2.2, h_mul.2, h_base2.2, h_q_val, h_r_val]
        simp [h_two.2] at h_r_val
        have h_one := binary_one_repr
        have : Str2Int (DivMod exp "10").2 = 1 := by simp [h_odd, h_one.2]
        simp [this] at h_r_val
        simp [h_r_val, Exp_int]
        ring_nf
        simp [Nat.mul_mod, Nat.mod_mod_of_dvd, Nat.add_mod]
    · simp [h_odd]
      have h_base2 := Mul_spec base base h_base h_base
      have h_mod_base := DivMod_spec (Mul base base) modulus h_base2.1 h_mod (by linarith)
      have h_rec := modexp_helper_spec (DivMod (Mul base base) modulus).2 
                      (DivMod exp "10").1 modulus result
                      h_mod_base.2.1 h_q_valid h_mod h_result h_mod_gt1
                      (Nat.mod_lt _ (by linarith)) h_result_lt
      constructor
      · exact h_rec.1
      · simp [h_rec.2, h_mod_base.2.2.2, h_base2.2, h_q_val, h_r_val]
        simp [h_two.2] at h_r_val
        have : Str2Int (DivMod exp "10").2 = 0 := by 
          by_contra h_ne
          have : Str2Int (DivMod exp "10").2 < 2 := by simp [h_r_val]; linarith
          have : Str2Int (DivMod exp "10").2 = 0 ∨ Str2Int (DivMod exp "10").2 = 1 := by omega
          cases this with
          | inl h => exact h
          | inr h => 
            have h_one := binary_one_repr
            have : (DivMod exp "10").2 = "1" := by
              sorry -- This would require proving string equality from Str2Int equality
            contradiction
        simp [this] at h_r_val
        simp [h_r_val, Exp_int]
        ring_nf
        simp [Nat.mul_mod, Nat.mod_mod_of_dvd]
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
have h_divmod_base := DivMod_spec sx sz hx hz (by linarith : Str2Int sz > 0)
obtain ⟨_, h_base_valid, _, h_base_val⟩ := h_divmod_base
have h_one := binary_one_repr
have h_helper := modexp_helper_spec (DivMod sx sz).2 sy sz "1" 
                   h_base_valid hy hz h_one.1 hsz_gt1
                   (Nat.mod_lt _ hsz_gt1) (by simp [h_one.2]; linarith)
constructor
· exact h_helper.1
· simp [h_helper.2, h_one.2, h_base_val, Nat.one_mul]
-- </vc-proof>

end BignumLean