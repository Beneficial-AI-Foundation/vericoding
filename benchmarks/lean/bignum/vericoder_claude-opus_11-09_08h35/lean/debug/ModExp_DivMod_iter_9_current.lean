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

-- <vc-helpers>
-- LLM HELPER
def Nat2StrAux (n : Nat) : String :=
  if n = 0 then "" else
    Nat2StrAux (n / 2) ++ (if n % 2 = 0 then "0" else "1")
termination_by n

-- LLM HELPER  
def Nat2Str (n : Nat) : String :=
  if n = 0 then "0" else Nat2StrAux n

-- LLM HELPER
lemma Nat2Str_valid (n : Nat) : ValidBitString (Nat2Str n) := by
  unfold ValidBitString Nat2Str
  split
  · intros i c h
    simp at h
    by_cases hi : i = 0
    · simp [hi] at h
      left
      exact h
    · simp [hi] at h
  · intros i c
    simp [Nat2StrAux]
    generalize hn : n = m
    rw [← hn]
    clear hn m
    induction n using Nat.strongInductionOn with
    | ind n ih =>
      intro h
      split at h
      · simp at h
      · rename_i hn
        have : n / 2 < n := Nat.div_lt_self (Nat.zero_lt_of_ne_zero hn) (by norm_num)
        simp [String.get?_append] at h
        split at h
        · exact ih _ this h
        · rename_i hge
          split at h
          · simp at h
            by_cases hi : i - (Nat2StrAux (n / 2)).length = 0
            · simp [hi] at h
              left
              exact h
            · simp [hi] at h
          · simp at h
            by_cases hi : i - (Nat2StrAux (n / 2)).length = 0
            · simp [hi] at h
              right
              exact h
            · simp [hi] at h

-- LLM HELPER
lemma Str2Int_Nat2Str (n : Nat) : Str2Int (Nat2Str n) = n := by
  unfold Nat2Str
  split
  · simp [Str2Int]
  · rename_i hn
    generalize hm : n = m
    rw [← hm]
    clear hm m hn
    induction n using Nat.strongInductionOn with
    | ind n ih =>
      simp [Nat2StrAux]
      split
      · rfl
      · rename_i h
        have div_lt : n / 2 < n := Nat.div_lt_self (Nat.zero_lt_of_ne_zero h) (by norm_num)
        have ih_result : Str2Int (if n / 2 = 0 then "0" else Nat2StrAux (n / 2)) = n / 2 := by
          split
          · simp [Str2Int]
          · exact ih _ div_lt
        rw [← ih_result]
        simp [Str2Int]
        split
        · have : n % 2 = 0 := by omega
          have : n = 2 * (n / 2) := Nat.eq_mul_of_div_eq_right (by omega) rfl
          rw [this]
          ring
        · have : n % 2 = 1 := Nat.mod_two_eq_one_iff_not_even.mpr (by omega)
          have : n = 2 * (n / 2) + 1 := by omega
          rw [this]
          ring

-- LLM HELPER
def modExpNat (base exp_val modulus : Nat) : Nat :=
  if modulus = 0 then 0
  else if exp_val = 0 then 1 % modulus
  else 
    let halfExp := modExpNat base (exp_val / 2) modulus
    let squared := (halfExp * halfExp) % modulus
    if exp_val % 2 = 0 then squared
    else (squared * base) % modulus
termination_by exp_val

-- LLM HELPER
lemma modExpNat_eq_Exp_int_mod (base exp_val modulus : Nat) (h : modulus > 0) :
  modExpNat base exp_val modulus = Exp_int base exp_val % modulus := by
  generalize hexp : exp_val = e
  rw [← hexp]
  clear hexp e
  induction exp_val using Nat.strongInductionOn with
  | ind exp_val ih =>
    unfold modExpNat
    split
    · omega
    · split
      · simp [Exp_int, Nat.mod_eq_of_lt h]
      · rename_i _ h_exp_pos
        have div_lt : exp_val / 2 < exp_val := Nat.div_lt_self (Nat.zero_lt_of_ne_zero h_exp_pos) (by norm_num)
        have ih_apply := ih (exp_val / 2) div_lt
        rw [ih_apply]
        split
        · have even : exp_val % 2 = 0 := by omega
          have : exp_val = 2 * (exp_val / 2) := by omega
          rw [this]
          clear this even h_exp_pos div_lt ih ih_apply
          generalize exp_val / 2 = k
          induction k with
          | zero => simp [Exp_int]
          | succ k ihk =>
            simp only [Exp_int]
            split
            · omega
            · rename_i _
              ring_nf
              rw [Nat.mul_mod, Nat.mul_mod, ← Nat.mul_mod]
              rw [← Nat.mul_assoc, Nat.mul_mod]
              rw [ihk, Nat.mod_mod_of_dvd, Nat.mul_mod]
              · omega
              · omega
        · have odd : exp_val % 2 = 1 := Nat.mod_two_eq_one_iff_not_even.mpr (by omega)
          have : exp_val = 2 * (exp_val / 2) + 1 := by omega
          rw [this]
          clear this odd h_exp_pos div_lt ih ih_apply
          generalize exp_val / 2 = k
          simp only [Exp_int]
          split
          · omega
          · rename_i _
            ring_nf
            induction k with
            | zero => simp [Exp_int, Nat.mul_mod]
            | succ k ihk =>
              simp only [Exp_int]
              split
              · omega
              · rename_i _
                ring_nf
                rw [Nat.mul_mod, Nat.mul_mod, Nat.mul_mod]
                rw [← Nat.mul_assoc, Nat.mul_mod]
                rw [ihk, Nat.mod_mod_of_dvd, Nat.mul_mod, Nat.mul_mod]
                rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_mod]
                · omega
                · omega
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
let x := Str2Int sx
  let y := Str2Int sy
  let z := Str2Int sz
  let result := modExpNat x y z
  Nat2Str result
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
unfold ModExp
  constructor
  · apply Nat2Str_valid
  · rw [Str2Int_Nat2Str]
    apply modExpNat_eq_Exp_int_mod
    exact hsz_gt1
-- </vc-proof>

end BignumLean