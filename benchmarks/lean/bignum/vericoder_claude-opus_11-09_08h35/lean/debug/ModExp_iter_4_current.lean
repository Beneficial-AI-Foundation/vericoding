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
    cases i <;> simp at h
    · left; exact h
  · intros i c h
    generalize hn : Int2Str.Int2StrAux n = s
    rw [← hn] at h
    clear h
    induction n using Nat.strong_induction_on generalizing s i c
    case _ n ih =>
      rw [Int2Str.Int2StrAux] at hn
      split at hn
      · simp at hn
        rw [← hn] at *
        simp
      · rw [← hn]
        clear hn
        rename_i hn
        simp [String.get?_append]
        intro i c
        split
        · intro h
          apply ih
          omega
          exact h
        · intro h
          rename_i hi
          cases' String.get?_ite_eq_some h with h h
          · right; exact h
          · left; exact h

-- LLM HELPER
lemma Str2Int_Int2Str_mod (n m : Nat) (hm : m > 0) : 
  Str2Int (Int2Str (n % m)) = n % m := by
  have h : n % m < m := Nat.mod_lt n hm
  generalize hn : n % m = k
  rw [← hn]
  clear hn n
  induction k using Nat.strong_induction_on
  case _ k ih =>
    unfold Int2Str
    split
    · rename_i h0
      simp [h0, Str2Int]
    · rename_i h0
      rw [Int2Str.Int2StrAux]
      split
      · contradiction
      · rename_i _
        unfold Str2Int
        simp [List.foldl_append, List.foldl]
        split
        · simp
          have : k / 2 < k := by
            cases k
            · contradiction
            · apply Nat.div_lt_self; omega; omega
          rw [← ih (k / 2) this]
          rw [← Int2Str.Int2StrAux]
          generalize Int2Str.Int2StrAux (k / 2) = s
          induction s.data generalizing k
          · simp [Str2Int]
          · rename_i c cs ih2
            simp [Str2Int, List.foldl] at *
            rw [ih2]
            omega
        · simp
          have : k / 2 < k := by
            cases k
            · contradiction
            · apply Nat.div_lt_self; omega; omega
          rw [← ih (k / 2) this]
          rw [← Int2Str.Int2StrAux]
          generalize Int2Str.Int2StrAux (k / 2) = s
          induction s.data generalizing k
          · simp [Str2Int]
            omega
          · rename_i c cs ih2
            simp [Str2Int, List.foldl] at *
            rw [ih2]
            omega

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
  induction exp using Nat.strong_induction_on generalizing base result
  case _ exp ih =>
    unfold modExpAux
    split
    · rename_i h
      simp [h, Exp_int]
    · rename_i h
      split
      · rename_i hodd
        have hdiv : exp / 2 < exp := Nat.div_lt_self (by omega) (by omega)
        rw [ih _ hdiv]
        unfold Exp_int
        rw [if_neg h]
        have : exp = 2 * (exp / 2) + 1 := by
          rw [Nat.mul_comm]
          exact Nat.div_add_mod exp 2 ▸ hodd ▸ rfl
        rw [this]
        clear this
        generalize exp / 2 = k
        induction k
        · simp [Exp_int, Nat.mul_mod, Nat.mod_mod_of_dvd, Nat.mod_mul_mod]
        · rename_i k ih2
          rw [Nat.succ_eq_add_one]
          ring_nf
          rw [Exp_int, if_neg (by omega : k + 1 ≠ 0)]
          ring_nf
          rw [← ih2]
          ring_nf
          rw [Nat.mul_mod, Nat.mod_mod_of_dvd, Nat.mul_mod]
          rw [Nat.mul_mod, Nat.mod_mod_of_dvd, Nat.mul_mod]
          ring_nf
          rw [← Nat.mul_mod, ← Nat.mul_mod]
          ring_nf
          rw [Nat.mul_mod, Nat.mul_mod, Nat.mod_mod_of_dvd]
          ring_nf
          omega
      · rename_i heven
        have hdiv : exp / 2 < exp := Nat.div_lt_self (by omega) (by omega)
        rw [ih _ hdiv]
        unfold Exp_int
        rw [if_neg h]
        have : exp = 2 * (exp / 2) := by
          have : exp % 2 = 0 := by
            cases Nat.mod_two_eq_zero_or_one exp
            · exact h_1
            · contradiction
          rw [← this, Nat.div_add_mod]
        rw [this]
        clear this
        generalize exp / 2 = k
        induction k
        · simp [Exp_int]
        · rename_i k ih2
          rw [Nat.succ_eq_add_one]
          ring_nf
          rw [Exp_int, if_neg (by omega : k + 1 ≠ 0)]
          ring_nf
          rw [← ih2]
          ring_nf
          rw [Nat.mul_mod, Nat.mod_mod_of_dvd, Nat.mul_mod]
          ring_nf
          omega
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