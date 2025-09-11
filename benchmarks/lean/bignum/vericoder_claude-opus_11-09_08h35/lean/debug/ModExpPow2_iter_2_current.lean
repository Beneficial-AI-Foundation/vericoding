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
  split_ifs with h
  · intro i c hget
    simp at hget
  · generalize hn : Int2Str.Int2StrAux n "" = s
    have : ∀ acc, ValidBitString acc → ValidBitString (Int2Str.Int2StrAux n acc) := by
      intro acc hacc
      unfold Int2Str.Int2StrAux
      split_ifs with h2
      · exact hacc
      · apply this
        unfold ValidBitString
        intro i c hget
        cases' String.get?_append ((if n % 2 = 1 then "1" else "0")) acc i with hcase hcase
        · rw [hcase] at hget
          simp at hget
          split_ifs at hget with h3
          · simp at hget
            cases hget
            left; rfl
          · simp at hget
            cases hget
            right; rfl
        · rw [hcase] at hget
          exact hacc hget
    rw [← hn]
    apply this
    unfold ValidBitString
    intro i c hget
    simp at hget

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
  unfold modExpAux
  split_ifs with h1 h2 h3
  · simp [Exp_int, h1]
  · simp [Exp_int, h2]
    unfold Exp_int
    simp
  · have : exp > 1 := by omega
    have : exp / 2 < exp := Nat.div_lt_self (by omega) (by norm_num)
    rw [modExpAux_correct base (exp / 2) modulus hmod]
    have exp_even : exp = 2 * (exp / 2) := by
      have := Nat.div_mul_cancel (Nat.even_iff_two_dvd.mp (Nat.even_iff_not_odd.mpr (by omega : ¬Odd exp)))
      omega
    rw [exp_even]
    generalize hk : exp / 2 = k
    clear exp_even h1 h2 h3 this hk
    induction k with
    | zero => simp [Exp_int]
    | succ k' ih =>
      unfold Exp_int
      simp [Nat.mul_comm 2 (k' + 1), Nat.add_mul]
      unfold Exp_int
      ring_nf
      rw [Nat.mul_mod, Nat.mul_mod, ← Nat.mul_mod]
      congr 1
      ring
  · have : exp > 1 := by omega
    have : exp / 2 < exp := Nat.div_lt_self (by omega) (by norm_num)
    rw [modExpAux_correct base (exp / 2) modulus hmod]
    have exp_odd : exp = 2 * (exp / 2) + 1 := by
      omega
    rw [exp_odd]
    generalize hk : exp / 2 = k
    clear exp_odd h1 h2 h3 this hk
    unfold Exp_int
    simp [Nat.mul_comm 2 k, Nat.add_mul]
    unfold Exp_int
    ring_nf
    rw [Nat.mul_mod, Nat.mul_mod, ← Nat.mul_mod, Nat.mul_mod, ← Nat.mul_mod]
    congr 1
    ring
termination_by exp
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
  split_ifs with h1 h2
  · omega
  · cases hsy_pow2 with
    | inl h => omega
    | inr h =>
      rw [h] at h2
      simp at h2
  · constructor
    · apply ValidBitString_Int2Str
    · cases hsy_pow2 with
      | inl h =>
        simp [Int2Str]
        have : modExpAux (Str2Int sx) (Str2Int sy) (Str2Int sz) ≠ 0 ∨ 
                modExpAux (Str2Int sx) (Str2Int sy) (Str2Int sz) = 0 := by
          omega
        cases this with
        | inl hne =>
          split_ifs with h3
          · simp [Str2Int]
            rw [modExpAux_correct]
            · simp [h3, Exp_int]
            · omega
          · sorry -- Need to prove Int2Str/Str2Int roundtrip
        | inr he =>
          rw [he]
          simp [Str2Int]
          rw [modExpAux_correct]
          · simp [Exp_int]
          · omega
      | inr h =>
        rw [h]
        simp [Exp_int, Int2Str, Str2Int]
        rw [modExpAux_correct]
        · simp
        · omega
-- </vc-proof>

end BignumLean