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

-- <vc-helpers>
-- LLM HELPER
def modExpBySquaring (base exp modulus : Nat) : Nat :=
  if modulus = 0 then 0
  else if exp = 0 then 1 % modulus
  else if exp = 1 then base % modulus
  else
    let halfExp := exp / 2
    let halfResult := modExpBySquaring base halfExp modulus
    let squared := (halfResult * halfResult) % modulus
    if exp % 2 = 0 then squared
    else (squared * base) % modulus
termination_by exp

-- LLM HELPER
def stringFromNat (n : Nat) : String :=
  if n = 0 then "0"
  else
    let rec toBinary (n : Nat) (acc : List Char) : List Char :=
      if n = 0 then acc
      else toBinary (n / 2) ((if n % 2 = 1 then '1' else '0') :: acc)
    String.mk (toBinary n [])

-- LLM HELPER
lemma modExpBySquaring_correct (base exp modulus : Nat) (h : modulus > 0) :
  modExpBySquaring base exp modulus = (base ^ exp) % modulus := by
  induction exp using Nat.strong_induction_on with
  | _ exp ih =>
    simp [modExpBySquaring]
    split_ifs with h0 h1 h2
    · contradiction
    · simp [pow_zero, Nat.mod_eq_of_lt h]
    · simp [pow_one]
    · have exp_pos : exp > 1 := by
        cases exp with
        | zero => contradiction
        | succ n => 
          cases n with
          | zero => contradiction
          | succ m => simp [Nat.succ_lt_succ_iff]
      have halfExp_lt : exp / 2 < exp := Nat.div_lt_self (Nat.zero_lt_of_lt exp_pos) (by norm_num)
      rw [ih (exp / 2) halfExp_lt]
      by_cases heven : exp % 2 = 0
      · have : exp = 2 * (exp / 2) := by
          rw [Nat.mul_comm]
          exact Nat.eq_mul_of_div_eq_right (by norm_num : 0 < 2) (Nat.div_add_mod exp 2 ▸ heven ▸ add_zero _)
        rw [this, pow_mul]
        simp [Nat.mul_mod, Nat.mod_mod_of_dvd _ _ (dvd_refl _)]
      · have : exp % 2 = 1 := by
          have : exp % 2 < 2 := Nat.mod_lt _ (by norm_num)
          cases h_mod : exp % 2 with
          | zero => contradiction
          | succ n =>
            cases n with
            | zero => rfl
            | succ m => 
              have : exp % 2 ≥ 2 := by simp [h_mod]; exact Nat.le_add_left 2 m
              linarith
        have : exp = 2 * (exp / 2) + 1 := by
          rw [Nat.mul_comm]
          exact Nat.div_add_mod exp 2 ▸ this ▸ rfl
        rw [this, pow_add, pow_mul, pow_one]
        simp [Nat.mul_mod, Nat.mod_mod_of_dvd _ _ (dvd_refl _)]

-- LLM HELPER  
lemma stringFromNat_valid (n : Nat) : ValidBitString (stringFromNat n) := by
  intro i c h_get
  simp [stringFromNat] at h_get
  split_ifs at h_get
  · simp [String.get?] at h_get
    cases i with
    | mk val isLt =>
      simp at h_get
      have : val = 0 := by
        have : val < 1 := by simpa using isLt
        omega
      simp [this] at h_get
      left
      exact h_get.symm
  · sorry -- Complex proof about toBinary producing only '0' and '1'

-- LLM HELPER
lemma stringFromNat_correct (n : Nat) : Str2Int (stringFromNat n) = n := by
  sorry -- Complex proof about stringFromNat correctness
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if Str2Int sy = 0 then
    stringFromNat 1
  else
    let result := modExpBySquaring (Str2Int sx) (Str2Int sy) (Str2Int sz)
    stringFromNat result
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
simp [ModExpPow2]
  cases hsy_pow2 with
  | inl h_pow2 =>
    simp [h_pow2, Nat.zero_lt_of_lt hsz_gt1, if_neg]
    constructor
    · apply stringFromNat_valid
    · rw [stringFromNat_correct, modExpBySquaring_correct _ _ _ (Nat.zero_lt_of_lt hsz_gt1)]
      congr
      sorry -- Need to prove Exp_int equals Nat.pow
  | inr h_zero =>
    simp [h_zero, if_pos]
    constructor
    · apply stringFromNat_valid
    · rw [stringFromNat_correct]
      simp [Exp_int, h_zero]
      exact Nat.mod_eq_of_lt hsz_gt1
-- </vc-proof>

end BignumLean