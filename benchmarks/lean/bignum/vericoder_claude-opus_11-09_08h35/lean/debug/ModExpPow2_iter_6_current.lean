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
  termination_by n

-- LLM HELPER
lemma ValidBitString_Int2Str (n : Nat) : ValidBitString (Int2Str n) := by
  unfold ValidBitString Int2Str
  intro i c hget
  split_ifs with h
  · simp at hget
    simp [String.get?] at hget
    split at hget
    · injection hget with heq
      left; exact heq
    · contradiction
  · have aux : ∀ m acc, (∀ j d, acc.get? j = some d → (d = '0' ∨ d = '1')) → 
            ∀ k e, (Int2Str.Int2StrAux m acc).get? k = some e → (e = '0' ∨ e = '1') := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro acc hacc k e hget'
        unfold Int2Str.Int2StrAux at hget'
        split_ifs at hget' with h2
        · exact hacc k e hget'
        · have hdiv : m / 2 < m := Nat.div_lt_self (Nat.zero_lt_of_ne_zero h2) (by norm_num)
          apply ih (m / 2) hdiv
          · intro j d hget''
            let prefix := if m % 2 = 1 then "1" else "0"
            have : (prefix ++ acc).get? j = some d := hget''
            by_cases hj : j < prefix.length
            · simp [String.get?, String.data_append] at this
              split at this
              · injection this with heq
                split_ifs at heq with hmod
                · left; exact heq
                · right; exact heq
              · contradiction
            · simp [String.get?, String.data_append] at this
              split at this
              · contradiction
              · split at this
                · exact hacc _ _ this
                · contradiction
          · exact hget'
    apply aux
    · intro j d hget'
      simp [String.get?] at hget'
    · exact hget

-- LLM HELPER  
lemma Str2Int_Int2Str (n : Nat) : Str2Int (Int2Str n) = n := by
  unfold Int2Str
  split_ifs with h
  · simp [h, Str2Int]
  · have aux : ∀ m acc, 
            Str2Int (Int2Str.Int2StrAux m acc) = m * (2 ^ acc.length) + Str2Int acc := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro acc
        unfold Int2Str.Int2StrAux
        split_ifs with h2
        · simp [h2]
          unfold Str2Int
          simp
        · have hdiv : m / 2 < m := Nat.div_lt_self (Nat.zero_lt_of_ne_zero h2) (by norm_num)
          let prefix := if m % 2 = 1 then "1" else "0"
          specialize ih (m / 2) hdiv (prefix ++ acc)
          rw [ih]
          unfold Str2Int
          simp [String.data_append, List.foldl_append]
          split_ifs with hmod
          · simp [String.length_append]
            have : m = 2 * (m / 2) + 1 := by
              have : m % 2 = 1 := hmod
              omega
            rw [this]
            ring
          · simp [String.length_append]
            have : m = 2 * (m / 2) := by
              have : m % 2 = 0 := by
                by_contra h'
                have : m % 2 < 2 := Nat.mod_lt m (by norm_num)
                omega
              omega
            rw [this]
            ring
    specialize aux n ""
    simp [Str2Int] at aux
    exact aux

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
  | _ exp ih =>
    unfold modExpAux Exp_int
    split_ifs with h1 h2 h3
    · simp [h1]
    · simp [h2]
    · have hdiv : exp / 2 < exp := Nat.div_lt_self (Nat.zero_lt_of_ne_zero h1) (by norm_num)
      rw [ih (exp / 2) hdiv]
      have : exp = 2 * (exp / 2) := by
        have : exp % 2 = 0 := by
          by_contra h'
          have : exp % 2 < 2 := Nat.mod_lt exp (by norm_num)
          omega
        omega
      rw [this]
      clear this h1 h2 h3 hdiv ih
      generalize hk : exp / 2 = k
      clear hk
      induction k with
      | zero => simp [Exp_int]
      | succ k' ih =>
        rw [Nat.mul_comm 2 (Nat.succ k'), Nat.succ_mul, Nat.add_comm]
        unfold Exp_int
        simp [Nat.succ_sub_one]
        rw [Nat.mul_comm 2 k', ← Nat.mul_assoc]
        unfold Exp_int at ih
        simp [Nat.succ_sub_one] at ih
        rw [Nat.mul_mod, Nat.mul_mod, ← Nat.mul_mod]
        congr 1
        ring
    · have hdiv : exp / 2 < exp := Nat.div_lt_self (Nat.zero_lt_of_ne_zero h1) (by norm_num)
      rw [ih (exp / 2) hdiv]
      have : exp = 2 * (exp / 2) + 1 := by
        have : exp % 2 = 1 := by
          by_contra h'
          push_neg at h'
          have : exp % 2 < 2 := Nat.mod_lt exp (by norm_num)
          omega
        omega
      rw [this]
      clear this h1 h2 h3 hdiv ih
      generalize hk : exp / 2 = k
      clear hk
      rw [Nat.mul_comm 2 k, Nat.add_comm]
      unfold Exp_int
      simp
      rw [Nat.mul_comm k 2]
      induction k with
      | zero => simp [Exp_int]
      | succ k' ih =>
        unfold Exp_int
        simp [Nat.succ_sub_one]
        rw [← Nat.mul_assoc, Nat.mul_comm _ base]
        rw [Nat.mul_mod, Nat.mul_mod, ← Nat.mul_mod, Nat.mul_mod, ← Nat.mul_mod]
        congr 1
        ring
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
    · rw [Str2Int_Int2Str]
      rw [modExpAux_correct]
      omega
-- </vc-proof>

end BignumLean