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
  intro i c hget
  split_ifs with h
  · simp at hget
    cases' i with i'
    · simp at hget
      injection hget with heq
      left; exact heq
    · simp at hget
  · have : ∀ m acc, (∀ j d, acc.get? j = some d → (d = '0' ∨ d = '1')) → 
            ∀ k e, (Int2Str.Int2StrAux m acc).get? k = some e → (e = '0' ∨ e = '1') := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro acc hacc k e hget'
        unfold Int2Str.Int2StrAux at hget'
        split_ifs at hget' with h2
        · exact hacc k e hget'
        · apply ih (m / 2) (Nat.div_lt_self (by omega) (by norm_num))
          intro j d hget''
          cases' String.get?_append ((if m % 2 = 1 then "1" else "0")) acc j with hcase hcase
          · rw [hcase] at hget''
            split_ifs at hget'' with h3
            · simp at hget''
              cases' j with j'
              · simp at hget''
                injection hget'' with heq
                left; exact heq
              · simp at hget''
            · simp at hget''
              cases' j with j'
              · simp at hget''
                injection hget'' with heq
                right; exact heq
              · simp at hget''
          · rw [hcase] at hget''
            exact hacc _ _ hget''
          · exact hget'
    apply this
    · intro j d hget'
      simp at hget'
    · exact hget

-- LLM HELPER
lemma Str2Int_Int2Str (n : Nat) : Str2Int (Int2Str n) = n := by
  unfold Int2Str
  split_ifs with h
  · simp [h, Str2Int]
  · have : ∀ m acc v, v = Str2Int acc → 
            Str2Int (Int2Str.Int2StrAux m acc) = m * (2 ^ acc.length) + v := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro acc v hv
        unfold Int2Str.Int2StrAux
        split_ifs with h2
        · simp [h2, hv]
          ring
        · have hdiv : m / 2 < m := Nat.div_lt_self (by omega) (by norm_num)
          specialize ih (m / 2) hdiv
          rw [ih]
          · unfold Str2Int
            split_ifs with h3
            · simp [String.data_append]
              rw [← hv]
              unfold Str2Int
              simp [List.foldl_append]
              have : acc.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 1 = 
                     2 ^ acc.length + v := by
                generalize hf : (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) = f
                have : ∀ l w, w = 2^l.length * 1 + v → 
                       l.foldl f w = 2^l.length * w + v := by
                  intro l
                  induction l with
                  | nil => simp
                  | cons h t ih =>
                    intro w hw
                    simp [List.foldl]
                    rw [ih]
                    · rw [← hf]
                      simp [hw]
                      ring
                    · rw [← hf]
                      simp [hw]
                      ring
                rw [this]
                · ring
                  have : m = 2 * (m / 2) + m % 2 := Nat.div_add_mod m 2
                  rw [this]
                  simp [h3]
                  ring
                · simp
                  rw [← hv]
                  unfold Str2Int
                  rfl
            · simp [String.data_append]
              rw [← hv]
              unfold Str2Int
              simp [List.foldl_append]
              have : acc.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = v := by
                rw [← hv]
                unfold Str2Int
                rfl
              rw [this]
              have : m = 2 * (m / 2) + m % 2 := Nat.div_add_mod m 2
              rw [this]
              split_ifs at h3
              · omega
              · simp
                ring
          · unfold Str2Int
            split_ifs with h3
            · simp [String.data_append]
              simp [List.foldl_append]
              ring
            · simp [String.data_append]
              simp [List.foldl_append]
              ring
    specialize this n "" 0
    simp at this
    exact this rfl

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
    unfold modExpAux
    split_ifs with h1 h2 h3
    · simp [Exp_int, h1]
    · simp [Exp_int, h2]
      unfold Exp_int
      simp
    · have hdiv : exp / 2 < exp := Nat.div_lt_self (by omega) (by norm_num)
      rw [ih (exp / 2) hdiv]
      have : exp = 2 * (exp / 2) := by
        have : exp % 2 = 0 := by
          split_ifs at h3 <;> omega
        exact Nat.eq_div_of_mul_eq_some_left (by norm_num) (by omega)
      rw [this]
      clear this h1 h2 h3 hdiv ih
      generalize hk : exp / 2 = k
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
    · have hdiv : exp / 2 < exp := Nat.div_lt_self (by omega) (by norm_num)
      rw [ih (exp / 2) hdiv]
      have : exp = 2 * (exp / 2) + 1 := by
        have : exp % 2 = 1 := by
          split_ifs at h3 <;> omega
        omega
      rw [this]
      clear this h1 h2 h3 hdiv ih
      generalize hk : exp / 2 = k
      unfold Exp_int
      simp [Nat.mul_comm 2 k, Nat.add_mul]
      unfold Exp_int
      ring_nf
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