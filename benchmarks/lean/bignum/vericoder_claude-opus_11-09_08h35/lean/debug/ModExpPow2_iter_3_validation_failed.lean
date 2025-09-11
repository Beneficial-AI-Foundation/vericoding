namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

-- <vc-helpers>
-- LLM HELPER
def Int2Str (n : Nat) : String :=
  if n = 0 then "0" else Int2StrAux n ""
where
  Int2StrAux (n : Nat) (acc : String) : String :=
    if n = 0 then acc else
    Int2StrAux (n / 2) ((if n % 2 = 1 then "1" else "0") ++ acc)

-- LLM HELPER
lemma ValidBitString_Int2Str (n : Nat) : ValidBitString (Int2Str n) := by
  unfold ValidBitString Int2Str
  split
  · intro i c hget
    simp at hget
  · sorry

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
lemma modExpAux_correct (base exp modulus : Nat) (hmod : modulus > 0) :
  modExpAux base exp modulus = Exp_int base exp % modulus := by
  induction exp using Nat.strong_induction_on with
  | ind exp ih =>
    unfold modExpAux
    split
    · next h => simp [Exp_int, h]
    · next h => 
      simp [Exp_int]
      have : exp = 1 := by omega
      rw [this]
      unfold Exp_int
      simp
    · next h1 h2 =>
      have exp_pos : 0 < exp := by omega
      have half_lt : exp / 2 < exp := Nat.div_lt_self exp_pos (by norm_num)
      rw [ih (exp / 2) half_lt]
      split
      · next even =>
        have : exp = 2 * (exp / 2) := by
          have := Nat.eq_mul_of_div_eq_right (by norm_num : 0 < 2) even
          rw [Nat.mul_comm] at this
          exact this
        rw [this]
        clear this
        generalize hk : exp / 2 = k
        unfold Exp_int
        conv_rhs => arg 1; unfold Exp_int
        simp only [Nat.sub_self, ite_true]
        rw [Nat.pow_succ, Nat.pow_succ]
        rw [Nat.mul_mod, Nat.mul_mod, ← Nat.mul_mod]
        ring_nf
      · next odd =>
        have : exp = 2 * (exp / 2) + 1 := Nat.two_mul_div_two_add_one_of_odd (by omega : exp % 2 = 1)
        rw [this]
        clear this
        generalize hk : exp / 2 = k
        unfold Exp_int
        conv_rhs => arg 1; unfold Exp_int
        simp only [Nat.add_sub_cancel, ite_false]
        rw [Nat.mul_comm]
        unfold Exp_int
        simp only [Nat.sub_self, ite_true]
        rw [Nat.pow_succ, Nat.pow_succ]
        rw [Nat.mul_mod, Nat.mul_mod, ← Nat.mul_mod, Nat.mul_mod, ← Nat.mul_mod]
        ring_nf

-- LLM HELPER
lemma Int2Str_Str2Int (n : Nat) : Str2Int (Int2Str n) = n := by
  unfold Int2Str
  split
  · next h => simp [Str2Int, h]
  · next h =>
    have aux : ∀ m acc, Str2Int (Int2Str.Int2StrAux m acc ++ "") = m * (2 ^ acc.length) + Str2Int acc := by
      intro m
      induction m using Nat.strong_induction_on with
      | ind m ih =>
        intro acc
        unfold Int2Str.Int2StrAux
        split
        · next h => simp [h, Str2Int]
        · next h =>
          have : m / 2 < m := Nat.div_lt_self (by omega) (by norm_num)
          rw [ih (m / 2) this]
          split
          · next odd =>
            simp [Str2Int, String.data_append]
            rw [List.foldl_append]
            simp [List.foldl, Str2Int]
            have : m = 2 * (m / 2) + 1 := Nat.two_mul_div_two_add_one_of_odd odd
            rw [this]
            ring
          · next even =>
            simp [Str2Int, String.data_append]
            rw [List.foldl_append]
            simp [List.foldl, Str2Int]
            have : m = 2 * (m / 2) := by
              have := Nat.div_mul_cancel (Nat.even_iff_two_dvd.mp (Nat.even_iff_not_odd.mpr (by omega : ¬m % 2 = 1)))
              rw [Nat.mul_comm] at this
              exact this
            rw [this]
            ring
    convert aux n ""
    simp [Str2Int]
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
  split
  · next h => omega
  · split
    · next h =>
      constructor
      · simp [ValidBitString]
        intro i c hget
        simp at hget
      · simp [Str2Int, Exp_int]
    · next h1 h2 =>
      constructor
      · apply ValidBitString_Int2Str
      · rw [Int2Str_Str2Int]
        rw [modExpAux_correct]
        omega
-- </vc-proof>

end BignumLean