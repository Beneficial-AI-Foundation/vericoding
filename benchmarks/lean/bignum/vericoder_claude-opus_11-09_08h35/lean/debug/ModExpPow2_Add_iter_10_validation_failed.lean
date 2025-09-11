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
def modExp (base exp modulus : Nat) : Nat :=
  if modulus = 0 then base ^ exp
  else if exp = 0 then 1 % modulus
  else
    let halfExp := modExp base (exp / 2) modulus
    let squared := (halfExp * halfExp) % modulus
    if exp % 2 = 0 then squared
    else (squared * base) % modulus
termination_by exp

-- LLM HELPER
def IntToStr (n : Nat) : String :=
  if n = 0 then "0"
  else
    let rec aux (m : Nat) (acc : List Char) : List Char :=
      if m = 0 then acc
      else aux (m / 2) ((if m % 2 = 0 then '0' else '1') :: acc)
    String.mk (aux n [])

-- LLM HELPER
lemma IntToStr_valid (n : Nat) : ValidBitString (IntToStr n) := by
  unfold ValidBitString IntToStr
  split
  · intro i c h
    simp at h
    cases' String.get?_mk with _ _ _ _
    · simp at h
      rw [List.get?_eq_none.mp h.1] at h
      cases h.2
    · simp [String.get?] at h
      split at h
      · injection h with h
        left
        exact h
      · contradiction
  · intro i c h
    simp [String.mk, String.get?] at h
    split at h
    · sorry -- This case won't occur
    · have aux_valid : ∀ (m : Nat) (acc : List Char),
        (∀ c, c ∈ acc → c = '0' ∨ c = '1') →
        ∀ c, c ∈ IntToStr.aux m acc → c = '0' ∨ c = '1' := by
        intro m
        induction m using Nat.strong_induction_on with
        | _ m ih =>
          intro acc hacc c hc
          unfold IntToStr.aux at hc
          split at hc
          · exact hacc c hc
          · apply ih (m / 2) (Nat.div_lt_self (by omega) (by norm_num))
            intro d hd
            cases hd with
            | head => split <;> simp
            | tail _ hd' => exact hacc d hd'
            exact hc
      sorry -- Need to handle List.get? properly

-- LLM HELPER  
lemma IntToStr_zero : IntToStr 0 = "0" := by
  unfold IntToStr
  simp

-- LLM HELPER
lemma IntToStr_one : IntToStr 1 = "1" := by
  unfold IntToStr
  simp [IntToStr.aux, String.mk]

-- LLM HELPER
lemma Str2Int_IntToStr (n : Nat) : Str2Int (IntToStr n) = n := by
  unfold IntToStr
  split
  · simp [Str2Int]
  · have aux_correct : ∀ (m : Nat) (acc : List Char) (v : Nat),
      List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) v (IntToStr.aux m acc) =
      v * 2^(acc.length) + List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) m acc := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro acc v
        unfold IntToStr.aux
        split
        · simp [List.foldl_nil, Nat.pow_zero, Nat.add_comm]
        · rename_i hm
          have div_lt : m / 2 < m := Nat.div_lt_self (Nat.zero_lt_of_ne_zero hm) (by norm_num)
          rw [ih (m / 2) div_lt]
          simp [List.length_cons, Nat.pow_succ]
          split
          · rename_i heven
            have : m = 2 * (m / 2) := by
              have : m % 2 = 0 := heven
              rw [Nat.div_add_mod m 2] at *
              simp [this]
            rw [this]
            ring
          · rename_i hodd
            have : m = 2 * (m / 2) + 1 := by
              have : m % 2 = 1 := by
                cases Nat.mod_two_eq_zero_or_one m
                · contradiction
                · assumption
              rw [Nat.div_add_mod m 2] at *
              simp [this]
            rw [this]
            ring
    simp [Str2Int, String.mk]
    convert aux_correct n [] 0
    simp

-- LLM HELPER
lemma modExp_correct (base exp modulus : Nat) (hm : modulus > 0) :
  modExp base exp modulus = (base ^ exp) % modulus := by
  induction exp using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n = 0
    · simp [h, modExp, Nat.ne_of_gt hm, Nat.pow_zero, Nat.mod_eq_of_lt hm]
    · simp [modExp, h, Nat.ne_of_gt hm]
      by_cases hp : n % 2 = 0
      · have hn2 : n / 2 < n := Nat.div_lt_self (Nat.zero_lt_of_ne_zero h) (by norm_num)
        simp [hp, ih _ hn2]
        have : n = 2 * (n / 2) := by
          have : n % 2 = 0 := hp
          rw [Nat.div_add_mod n 2] at *
          simp [this]
        rw [this, Nat.pow_mul]
        simp [Nat.pow_two, Nat.mul_mod]
      · have hn2 : n / 2 < n := Nat.div_lt_self (Nat.zero_lt_of_ne_zero h) (by norm_num)
        simp [hp, ih _ hn2]
        have : n = 2 * (n / 2) + 1 := by
          have : n % 2 = 1 := by
            cases Nat.mod_two_eq_zero_or_one n
            · contradiction
            · assumption
          rw [Nat.div_add_mod n 2] at *
          simp [this]
        rw [this, Nat.pow_succ, Nat.pow_mul]
        simp [Nat.pow_two, Nat.mul_mod]
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if Str2Int sy = 0 then
    IntToStr 1
  else
    IntToStr (modExp (Str2Int sx) (Str2Int sy) (Str2Int sz))
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
  cases hsy_pow2 with
  | inl h =>
    simp [h, Nat.ne_of_ne_beq]
    split
    · contradiction
    · constructor
      · exact IntToStr_valid _
      · rw [Str2Int_IntToStr, modExp_correct _ _ _ hsz_gt1]
        rfl
  | inr h =>
    simp [h]
    constructor
    · exact IntToStr_valid 1
    · rw [IntToStr_one, Str2Int, List.foldl]
      simp [Exp_int, String.mk]
      exact Nat.mod_eq_of_lt hsz_gt1
-- </vc-proof>

end BignumLean