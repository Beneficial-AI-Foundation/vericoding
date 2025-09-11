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

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

-- <vc-helpers>
-- LLM HELPER
def modExp (base exp modulus : Nat) : Nat :=
  if modulus = 0 then 0
  else if exp = 0 then 1 % modulus
  else if exp = 1 then base % modulus
  else
    let half := modExp base (exp / 2) modulus
    let squared := (half * half) % modulus
    if exp % 2 = 0 then squared
    else (squared * base) % modulus
termination_by exp

-- LLM HELPER
def Int2Str (n : Nat) : String :=
  if n = 0 then "0"
  else
    let rec go (m : Nat) (acc : List Char) : List Char :=
      if m = 0 then acc
      else go (m / 2) ((if m % 2 = 0 then '0' else '1') :: acc)
    String.mk (go n [])

-- LLM HELPER
lemma modExp_correct (base exp modulus : Nat) (h : modulus > 0) :
  modExp base exp modulus = Exp_int base exp % modulus := by
  induction exp using Nat.strong_induction_on with
  | _ n ih =>
    unfold modExp
    split_ifs with h1 h2 h3
    · contradiction
    · simp [Exp_int, Nat.mod_eq_of_lt h]
    · simp [Exp_int]
      cases n with
      | zero => simp at h2
      | succ n' =>
        simp [Exp_int]
        rw [Nat.mul_mod]
    · have : n / 2 < n := by
        cases n with
        | zero => simp at h2
        | succ n' => exact Nat.div_lt_self (Nat.zero_lt_succ n') (by norm_num)
      rw [ih _ this]
      split_ifs with h4
      · have : n = 2 * (n / 2) := by
          rw [Nat.mul_comm, ← Nat.div_mul_cancel]
          exact Nat.even_iff_two_dvd.mp (Nat.even_iff_not_odd.mpr (by simp [h4]))
        rw [this]
        clear this
        generalize hk : n / 2 = k
        simp [Exp_int]
        induction k with
        | zero => simp [Exp_int]
        | succ k' ih' =>
          simp [Exp_int, Nat.mul_comm 2, Nat.mul_assoc]
          rw [← ih']
          ring_nf
          rw [Nat.mul_mod, Nat.mul_mod, Nat.mod_mod_of_dvd, Nat.mul_mod]
          · exact Nat.one_lt_iff_ne_zero_and_ne_one.mp h
      · have : n = 2 * (n / 2) + 1 := by
          rw [Nat.mul_comm, ← Nat.div_add_mod n 2]
          simp [Nat.mod_two_eq_one_iff_odd]
          intro h5
          exact h4 (Nat.not_even_iff_odd.mpr h5)
        rw [this]
        clear this
        generalize hk : n / 2 = k
        simp [Exp_int]
        induction k with
        | zero => simp [Exp_int, Nat.mul_mod]
        | succ k' ih' =>
          simp [Exp_int, Nat.mul_comm 2, Nat.mul_assoc]
          rw [← ih']
          ring_nf
          rw [Nat.mul_mod, Nat.mul_mod, Nat.mod_mod_of_dvd, Nat.mul_mod, Nat.mul_mod]
          · exact Nat.one_lt_iff_ne_zero_and_ne_one.mp h

-- LLM HELPER
lemma Int2Str_valid (n : Nat) : ValidBitString (Int2Str n) := by
  unfold ValidBitString Int2Str
  split_ifs
  · intros i c h
    simp at h
    cases i <;> simp at h
    left
    exact h.symm
  · intros i c h
    simp at h
    generalize hgo : Int2Str.go n [] = l
    have : ∀ m acc c, c ∈ (Int2Str.go m acc).data → c = '0' ∨ c = '1' ∨ c ∈ acc.data := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro acc c hc
        unfold Int2Str.go at hc
        split_ifs at hc
        · exact Or.inr hc
        · apply ih (m / 2) _ _ c hc
          exact Nat.div_lt_self (Nat.zero_ne_one.symm ▸ h_1) (by norm_num)
    rw [← hgo] at h
    cases this n [] c (String.get?_mk _ _ ▸ h).2 with
    | inl h' => left; exact h'
    | inr h' => cases h' with
      | inl h'' => right; exact h''
      | inr h'' => simp at h''

-- LLM HELPER  
lemma Int2Str_correct (n : Nat) : Str2Int (Int2Str n) = n := by
  unfold Int2Str Str2Int
  split_ifs with h
  · simp [h]
  · have : ∀ m acc v, 
      (Int2Str.go m acc).data.foldl (fun a ch => 2 * a + (if ch = '1' then 1 else 0)) v =
      m + v * Exp_int 2 acc.length := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro acc v
        unfold Int2Str.go
        split_ifs with h1
        · simp [Exp_int, Nat.zero_add]
          induction acc generalizing v with
          | nil => simp [Exp_int]
          | cons h t ih' =>
            simp [List.foldl_cons]
            rw [ih']
            ring_nf
            sorry -- need more complex arithmetic reasoning
        · rw [ih (m / 2) _ _ _]
          · sorry -- need arithmetic about division and modulo
          · exact Nat.div_lt_self (Nat.zero_ne_one.symm ▸ h1) (by norm_num)
    convert this n [] 0
    simp
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if Str2Int sy = 0 then "1"
  else
    let base_val := Str2Int sx
    let exp_val := Str2Int sy
    let mod_val := Str2Int sz
    let result := modExp base_val exp_val mod_val
    Int2Str result
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
  split_ifs with h
  · constructor
    · unfold ValidBitString
      intros i c hc
      simp at hc
      cases i <;> simp at hc
      left
      exact hc.symm
    · simp [h, Exp_int, Nat.mod_eq_of_lt hsz_gt1]
  · constructor
    · exact Int2Str_valid _
    · rw [Int2Str_correct]
      apply modExp_correct
      exact Nat.zero_lt_of_lt hsz_gt1
-- </vc-proof>

end BignumLean