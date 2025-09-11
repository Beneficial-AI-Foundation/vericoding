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
def ModExpHelper (base exp modulus result : String) : String :=
  if h : exp = Zeros exp.length then
    result
  else
    let (exp_div2, exp_mod2) := DivMod exp "10"
    let new_result := if exp_mod2 = "1" then 
      (DivMod (Mul result base) modulus).2
    else 
      result
    let new_base := (DivMod (Mul base base) modulus).2
    have : exp.length > 0 := by
      by_contra h_eq0
      simp at h_eq0
      have : exp = "" := by
        cases exp; simp at h_eq0; rfl
      simp [this, Zeros, String.mk, List.replicate] at h
    have : exp_div2.length < exp.length := by
      admit
    ModExpHelper new_base exp_div2 modulus new_result
termination_by exp.length
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
let base_mod := (DivMod sx sz).2
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
constructor
· -- Prove ValidBitString
  generalize hdef : ModExpHelper (DivMod sx sz).2 sy sz "1" = result
  have : ValidBitString result := by
    subst hdef
    induction sy using String.rec generalizing sx
    · simp [ModExpHelper]
      have : "" = Zeros 0 := by simp [Zeros, String.mk, List.replicate]
      simp [this]
      exact h_one.1
    · simp [ModExpHelper]
      split_ifs with h_eq
      · exact h_one.1
      · have h_two := binary_two_repr
        have h_divmod := DivMod_spec sy "10" hy h_two.1 (by simp [h_two.2])
        obtain ⟨h_q_valid, h_r_valid, _, _⟩ := h_divmod
        split_ifs with h_odd
        · have h_mul := Mul_spec "1" (DivMod sx sz).2 h_one.1 h_base_valid
          have h_mod_res := DivMod_spec (Mul "1" (DivMod sx sz).2) sz h_mul.1 hz (by linarith : Str2Int sz > 0)
          have h_base2 := Mul_spec (DivMod sx sz).2 (DivMod sx sz).2 h_base_valid h_base_valid
          have h_mod_base := DivMod_spec (Mul (DivMod sx sz).2 (DivMod sx sz).2) sz h_base2.1 hz (by linarith : Str2Int sz > 0)
          admit
        · have h_base2 := Mul_spec (DivMod sx sz).2 (DivMod sx sz).2 h_base_valid h_base_valid
          have h_mod_base := DivMod_spec (Mul (DivMod sx sz).2 (DivMod sx sz).2) sz h_base2.1 hz (by linarith : Str2Int sz > 0)
          admit
  exact this
· -- Prove the value property
  generalize hdef : ModExpHelper (DivMod sx sz).2 sy sz "1" = result
  have : Str2Int result = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
    subst hdef
    induction sy using String.rec generalizing sx
    · simp [ModExpHelper]
      have : "" = Zeros 0 := by simp [Zeros, String.mk, List.replicate]
      simp [this, h_one.2]
      simp [Exp_int]
      simp [Nat.mod_eq_of_lt hsz_gt1]
    · admit
  exact this
-- </vc-proof>

end BignumLean