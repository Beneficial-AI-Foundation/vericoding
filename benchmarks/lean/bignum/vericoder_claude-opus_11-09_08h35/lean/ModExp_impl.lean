namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

-- <vc-helpers>
-- LLM HELPER
def Int2Str (n : Nat) : String :=
  if n = 0 then "0" else Int2StrAux n
where
  Int2StrAux (n : Nat) : String :=
    if n = 0 then "" else Int2StrAux (n / 2) ++ (if n % 2 = 0 then "0" else "1")

-- LLM HELPER
lemma Int2Str_valid (n : Nat) : ValidBitString (Int2Str n) := by
  unfold Int2Str ValidBitString
  split
  · intros i c h
    simp at h
    cases i with
    | zero => 
      simp at h
      left
      exact h
    | succ j => simp at h
  · intros i c h
    have : ValidBitString (Int2Str.Int2StrAux n) := by
      clear h i c
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        unfold ValidBitString Int2Str.Int2StrAux
        split
        · intros i c h
          simp at h
        · intros i c
          simp [String.get?_append]
          split
          · intro h
            apply ih
            apply Nat.div_lt_self
            · cases n with
              | zero => contradiction
              | succ n' => omega
            · omega
            · exact h
          · split
            · intro h
              simp at h
              cases h with
              | inl h => left; exact h
              | inr h => right; exact h
            · intro h
              simp at h
              cases h with
              | inl h => left; exact h
              | inr h => right; exact h
    exact this h

-- LLM HELPER
lemma Str2Int_Int2Str_mod (n m : Nat) (hm : m > 0) : 
  Str2Int (Int2Str (n % m)) = n % m := by
  have h : n % m < m := Nat.mod_lt n hm
  generalize hn : n % m = k
  rw [← hn]
  clear hn n
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    unfold Int2Str
    split
    · simp [Str2Int]
      rename_i h0
      exact h0
    · unfold Int2Str.Int2StrAux
      split
      · contradiction
      · unfold Str2Int
        simp [List.foldl_append, List.foldl]
        have hdiv : k / 2 < k := by
          cases k with
          | zero => contradiction
          | succ k' => 
            apply Nat.div_lt_self
            · omega
            · omega
        have ih_result := ih (k / 2) hdiv
        unfold Int2Str at ih_result
        split at ih_result
        · have k_div_zero : k / 2 = 0 := by rename_i h; exact h
          have : k < 2 := by
            have : k / 2 * 2 ≤ k := Nat.div_mul_le_self k 2
            rw [k_div_zero] at this
            simp at this
            exact this
          cases k with
          | zero => contradiction
          | succ k' =>
            cases k' with
            | zero => 
              simp [Str2Int]
              split <;> simp
            | succ _ => omega
        · rw [← ih_result]
          clear ih_result
          generalize haux : Int2Str.Int2StrAux (k / 2) = s
          have : Str2Int s = k / 2 := by
            rw [← haux]
            apply ih
            exact hdiv
          rw [this]
          split
          · have k_mod_zero : k % 2 = 0 := by rename_i h; exact h
            have : k = k / 2 * 2 := by
              rw [← Nat.add_zero (k / 2 * 2)]
              rw [← k_mod_zero]
              exact Nat.div_add_mod k 2
            rw [this]
            ring
          · have : k % 2 = 1 := by
              cases Nat.mod_two_eq_zero_or_one k with
              | inl h => contradiction
              | inr h => exact h
            have : k = k / 2 * 2 + 1 := by
              rw [← this]
              exact Nat.div_add_mod k 2
            rw [this]
            ring

-- LLM HELPER
def modExpAux (base exp modulus result : Nat) : Nat :=
  if h : exp = 0 then result
  else if exp % 2 = 1 then
    have : exp / 2 < exp := Nat.div_lt_self (by omega : 0 < exp) (by omega : 1 < 2)
    modExpAux ((base * base) % modulus) (exp / 2) modulus ((result * base) % modulus)
  else
    have : exp / 2 < exp := Nat.div_lt_self (by omega : 0 < exp) (by omega : 1 < 2)
    modExpAux ((base * base) % modulus) (exp / 2) modulus result
termination_by exp

-- LLM HELPER
lemma modExpAux_spec (base exp modulus result : Nat) (hm : modulus > 1) :
  modExpAux base exp modulus result = (result * Exp_int base exp) % modulus := by
  induction exp using Nat.strong_induction_on generalizing base result with
  | _ exp ih =>
    unfold modExpAux
    split
    · simp [Exp_int]
      rename_i h
      rw [h]
      simp
    · split
      · have hdiv : exp / 2 < exp := by
          apply Nat.div_lt_self
          · omega
          · omega
        rw [ih _ hdiv]
        unfold Exp_int
        split
        · contradiction
        · have : exp = 2 * (exp / 2) + 1 := by
            rw [Nat.mul_comm]
            rename_i _ h
            have : exp % 2 = 1 := h
            rw [← this]
            exact Nat.div_add_mod exp 2
          conv_rhs => rw [this]
          clear this
          generalize hk : exp / 2 = k
          clear hdiv ih hk
          induction k with
          | zero =>
            simp [Exp_int]
            rw [Nat.mul_mod, Nat.mod_mod_of_dvd]
            · rw [Nat.mul_mod]
            · omega
          | succ k ih2 =>
            rw [Nat.mul_add, Nat.mul_one]
            rw [Exp_int, if_neg (by omega : k.succ ≠ 0)]
            conv_rhs => rw [Nat.add_comm, Exp_int, if_neg (by omega : k + 1 ≠ 0)]
            rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
            rw [Nat.mul_mod, Nat.mul_mod]
            rw [Nat.mod_mod_of_dvd, Nat.mod_mod_of_dvd] <;> try omega
            rw [Nat.mul_mod (result % modulus)]
            rw [← Nat.mul_assoc base, ← Nat.mul_assoc base]
            rw [Nat.mul_comm base, Nat.mul_assoc]
            rw [Nat.mul_mod, Nat.mod_mod_of_dvd, Nat.mul_mod] <;> try omega
      · have hdiv : exp / 2 < exp := by
          apply Nat.div_lt_self
          · omega
          · omega
        rw [ih _ hdiv]
        unfold Exp_int
        split
        · contradiction
        · have : exp = 2 * (exp / 2) := by
            have : exp % 2 = 0 := by
              cases Nat.mod_two_eq_zero_or_one exp with
              | inl h => exact h
              | inr h => contradiction
            rw [← this]
            exact Nat.div_add_mod exp 2
          conv_rhs => rw [this]
          clear this
          generalize hk : exp / 2 = k
          clear hdiv ih hk
          induction k with
          | zero =>
            simp [Exp_int]
          | succ k ih2 =>
            rw [Nat.mul_succ]
            rw [Exp_int, if_neg (by omega : k.succ ≠ 0)]
            conv_rhs => rw [Exp_int, if_neg (by omega : k + 1 ≠ 0)]
            rw [Nat.mul_assoc, Nat.mul_assoc]
            rw [Nat.mul_mod]
            rw [← Nat.mul_assoc base]
            rw [Nat.mul_mod, Nat.mod_mod_of_dvd, Nat.mul_mod] <;> try omega
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if Str2Int sz <= 1 then "0" else
    let x := Str2Int sx % Str2Int sz
    let y := Str2Int sy
    let z := Str2Int sz
    Int2Str (modExpAux x y z 1)
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
unfold ModExp
  split
  · rename_i h
    omega
  · constructor
    · apply Int2Str_valid
    · rw [Str2Int_Int2Str_mod _ _ hsz_gt1]
      rw [modExpAux_spec]
      · simp [Nat.mod_mod_of_dvd]
        omega
      · exact hsz_gt1
-- </vc-proof>

end BignumLean