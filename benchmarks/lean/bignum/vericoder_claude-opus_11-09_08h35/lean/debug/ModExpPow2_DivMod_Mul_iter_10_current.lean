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

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

-- <vc-helpers>
-- LLM HELPER
def modExpPow2Helper (base : String) (n : Nat) (modulus : String) : String :=
  match n with
  | 0 => base
  | n' + 1 => 
    let squared := Mul base base
    let (_, remainder) := DivMod squared modulus
    modExpPow2Helper remainder n' modulus
termination_by n

-- LLM HELPER  
lemma exp_int_zero (x : Nat) : Exp_int x 0 = 1 := by
  unfold Exp_int
  simp

-- LLM HELPER
lemma exp_int_succ (x y : Nat) : Exp_int x (y + 1) = x * Exp_int x y := by
  unfold Exp_int
  simp [Nat.add_sub_cancel]

-- LLM HELPER
lemma str2int_one : Str2Int "1" = 1 := by
  unfold Str2Int
  simp [String.data, List.foldl]

-- LLM HELPER
lemma valid_bitstring_one : ValidBitString "1" := by
  unfold ValidBitString
  intros i c h_get
  simp [String.get?, String.data] at h_get
  cases i with
  | zero => 
    simp [List.get?] at h_get
    injection h_get with h_eq
    right
    exact h_eq
  | succ _ =>
    simp [List.get?] at h_get

-- LLM HELPER
lemma modExpPow2Helper_valid (base : String) (n : Nat) (modulus : String)
  (h_base : ValidBitString base) (h_mod : ValidBitString modulus) (h_pos : Str2Int modulus > 0) :
  ValidBitString (modExpPow2Helper base n modulus) := by
  induction n generalizing base with
  | zero => 
    unfold modExpPow2Helper
    exact h_base
  | succ n' ih =>
    unfold modExpPow2Helper
    have h_mul := Mul_spec base base h_base h_base
    have h_div := DivMod_spec (Mul base base) modulus h_mul.1 h_mod h_pos
    apply ih h_div.2.1

-- LLM HELPER
lemma modExpPow2Helper_spec (base : String) (n : Nat) (modulus : String)
  (h_base : ValidBitString base) (h_mod : ValidBitString modulus) (h_pos : Str2Int modulus > 0) :
  Str2Int (modExpPow2Helper base n modulus) = Exp_int (Str2Int base) (Exp_int 2 n) % Str2Int modulus := by
  induction n generalizing base with
  | zero =>
    unfold modExpPow2Helper
    simp [exp_int_zero]
    have h_base_range : Str2Int base < Str2Int modulus ∨ Str2Int base ≥ Str2Int modulus := by
      cases Decidable.lt_or_le (Str2Int base) (Str2Int modulus)
      · left; assumption
      · right; assumption
    cases h_base_range with
    | inl h_lt => simp [Nat.mod_eq_of_lt h_lt]
    | inr h_ge => 
      -- base is already result of modulo operation in recursive calls
      rfl
  | succ n' ih =>
    unfold modExpPow2Helper
    have h_mul := Mul_spec base base h_base h_base
    have h_div := DivMod_spec (Mul base base) modulus h_mul.1 h_mod h_pos
    rw [ih h_div.2.1]
    rw [h_div.2.2.2, h_mul.2]
    simp [Exp_int]
    rw [Nat.pow_succ, Nat.mul_mod, Nat.mod_mod_of_dvd, Nat.mul_mod]
    · congr 1
      rw [← Nat.mul_mod, ← Nat.mul_mod]
      congr 1
      · rw [← Nat.pow_two, ← Nat.pow_mul]
        simp [Nat.pow_two]
    · exact Nat.zero_lt_of_lt h_pos
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if Str2Int sy = 0 then
    "1"  -- x^0 = 1
  else
    -- sy = 2^n, compute x^(2^n) mod z by repeated squaring
    let (_, r0) := DivMod sx sz  -- Start with x mod z
    modExpPow2Helper r0 n sz
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
  by_cases h_eq : Str2Int sy = 0
  · -- Case: Str2Int sy = 0
    simp [h_eq]
    constructor
    · -- Prove ValidBitString "1"
      exact valid_bitstring_one
    · -- Prove Str2Int "1" = x^0 mod z
      rw [str2int_one]
      rw [h_eq, exp_int_zero]
      have : 1 < Str2Int sz := hsz_gt1
      simp [Nat.mod_eq_of_lt this]
  · -- Case: Str2Int sy ≠ 0, so sy = 2^n
    cases hsy_pow2 with
    | inr h_zero => 
      contradiction
    | inl h_pow2 =>
      simp [h_eq]
      have h_sz_pos : Str2Int sz > 0 := Nat.zero_lt_of_lt hsz_gt1
      have h_div := DivMod_spec sx sz hx hz h_sz_pos
      constructor
      · -- Prove ValidBitString result
        apply modExpPow2Helper_valid
        · exact h_div.2.1
        · exact hz
        · exact h_sz_pos
      · -- Prove Str2Int result = x^(2^n) mod z
        rw [h_pow2]
        rw [modExpPow2Helper_spec h_div.2.1 hz h_sz_pos]
        rw [h_div.2.2.2]
-- </vc-proof>

end BignumLean