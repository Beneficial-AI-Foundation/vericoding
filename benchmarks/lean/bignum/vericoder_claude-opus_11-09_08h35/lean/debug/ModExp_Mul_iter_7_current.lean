namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

-- <vc-helpers>
-- LLM HELPER
def Nat2Str (n : Nat) : String :=
  if n = 0 then "0" else
    let rec toBinary (m : Nat) (acc : String) : String :=
      if m = 0 then acc
      else toBinary (m / 2) ((if m % 2 = 1 then "1" else "0") ++ acc)
    toBinary n ""

-- LLM HELPER
lemma Nat2Str_valid (n : Nat) : ValidBitString (Nat2Str n) := by
  unfold ValidBitString Nat2Str
  split_ifs
  · intros i c h
    simp at h
    cases i <;> simp at h
  · intro i c
    generalize hm : toBinary n "" = s
    have : ∀ m acc, ValidBitString acc → ValidBitString (toBinary m acc) := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro acc hacc
        unfold toBinary
        split_ifs with h
        · exact hacc
        · apply ih (m / 2) (Nat.div_lt_self (Nat.zero_lt_of_ne_zero h) (by norm_num))
          unfold ValidBitString
          intros j d hget
          cases' String.get?_append ((if m % 2 = 1 then "1" else "0")) acc j with hj hj
          · rw [hget] at hj
            injection hj with hj
            split_ifs at hj <;> simp at hj <;> [left; right] <;> exact hj
          · rw [hget] at hj
            exact hacc hj
    rw [← hm]
    apply this
    unfold ValidBitString
    intros i c h
    simp at h

-- LLM HELPER  
lemma Str2Int_Nat2Str (n : Nat) : Str2Int (Nat2Str n) = n := by
  unfold Nat2Str
  split_ifs with h
  · simp [h, Str2Int]
  · have : ∀ m acc, Str2Int (toBinary m acc) = m * (2 ^ acc.length) + Str2Int acc := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro acc
        unfold toBinary
        split_ifs with hm
        · simp [hm]
          unfold Str2Int
          cases acc.data <;> simp
        · have div_lt : m / 2 < m := Nat.div_lt_self (Nat.zero_lt_of_ne_zero hm) (by norm_num)
          rw [ih (m / 2) div_lt]
          unfold Str2Int
          simp [List.foldl_append]
          split_ifs with hmod
          · simp [List.foldl]
            ring_nf
            rw [Nat.div_add_mod m 2]
            simp [hmod]
            ring
          · simp [List.foldl]
            ring_nf
            have : m % 2 = 0 := by
              cases Nat.mod_two_eq_zero_or_one m <;> simp [*] at hmod
            rw [Nat.div_add_mod m 2, this]
            ring
    simp [this, Str2Int]

-- LLM HELPER
def ModMul (s1 s2 sm : String) : String :=
  Nat2Str ((Str2Int s1 * Str2Int s2) % Str2Int sm)

-- LLM HELPER
lemma ModMul_valid (s1 s2 sm : String) : ValidBitString (ModMul s1 s2 sm) := by
  unfold ModMul
  exact Nat2Str_valid _

-- LLM HELPER
lemma ModMul_spec (s1 s2 sm : String) :
  Str2Int (ModMul s1 s2 sm) = (Str2Int s1 * Str2Int s2) % Str2Int sm := by
  unfold ModMul
  exact Str2Int_Nat2Str _
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if sy = "0" then "1"
  else if sy = "1" then Nat2Str (Str2Int sx % Str2Int sz)
  else
    let sy_half := Nat2Str (Str2Int sy / 2)
    let temp := ModExp sx sy_half sz
    let squared := ModMul temp temp sz
    if Str2Int sy % 2 = 0 then squared
    else ModMul squared sx sz
termination_by Str2Int sy
decreasing_by
  simp_wf
  have : Str2Int sy ≠ 0 := by
    intro h
    have : sy = "0" ∨ sy.data = [] := by
      unfold Str2Int at h
      cases sy.data with
      | nil => right; rfl
      | cons c cs =>
        simp at h
        left; ext; simp; exact h
    cases this
    · contradiction
    · unfold Str2Int at h; simp [*] at h
  exact Nat.div_lt_self (Nat.zero_lt_of_ne_zero this) (by norm_num)
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
generalize hn : Str2Int sy = n
induction n using Nat.strong_induction_on generalizing sx sy sz with
| _ n ih =>
  unfold ModExp
  split_ifs with h0 h1
  · constructor
    · unfold ValidBitString; intros i c hget; simp at hget; cases i <;> simp at hget
    · simp [h0, Str2Int, Exp_int]
  · constructor
    · exact Nat2Str_valid _
    · rw [Str2Int_Nat2Str]
      have : Str2Int sy = 1 := by
        unfold Str2Int at *
        cases sy.data with
        | nil => simp at hsy_pos
        | cons c cs =>
          simp at h1 ⊢
          cases h1 with
          | inl h => simp [h]
          | inr h =>
            obtain ⟨hc, hcs⟩ := h
            simp [hc]
            have : cs = [] := by
              by_contra hne
              cases cs with
              | nil => contradiction
              | cons d ds => simp at hcs
            simp [this]
      simp [this, Exp_int]
  · have sy_pos : 0 < Str2Int sy := by
      by_contra h
      simp at h
      have : sy = "0" ∨ sy.data = [] := by
        unfold Str2Int at h
        cases sy.data with
        | nil => right; rfl
        | cons c cs =>
          simp at h
          left
          ext
          simp
          exact h
      cases this
      · contradiction
      · simp [*] at hsy_pos
    have div_lt : Str2Int sy / 2 < Str2Int sy := Nat.div_lt_self sy_pos (by norm_num)
    have ih_apply := ih (Str2Int sy / 2) (by rw [← hn]; exact div_lt) sx (Nat2Str (Str2Int sy / 2)) sz 
                        (Nat2Str_valid _) hy hz
    rw [Str2Int_Nat2Str] at ih_apply
    have pos_len : 0 < (Nat2Str (Str2Int sy / 2)).length := by
      unfold Nat2Str
      split_ifs with h
      · simp at div_lt
        have : Str2Int sy / 2 ≠ 0 := Nat.ne_of_gt div_lt
        contradiction
      · simp
    obtain ⟨valid_temp, spec_temp⟩ := ih_apply pos_len hsz_gt1 rfl
    split_ifs with heven
    · constructor
      · exact ModMul_valid _ _ _
      · rw [ModMul_spec, spec_temp]
        rw [← hn]
        have : n = 2 * (n / 2) := by
          rw [← hn] at heven
          rw [← Nat.div_add_mod n 2, heven]
          simp
        rw [this]
        clear this
        generalize hk : n / 2 = k
        rw [← hk] at spec_temp
        simp [Exp_int]
        by_cases hz : k = 0
        · simp [hz, Exp_int]
        · rw [Exp_int]
          split_ifs
          · contradiction
          · simp [Nat.pow_succ]
            ring_nf
            rw [Nat.mul_mod, Nat.mod_mod_of_dvd, ← Nat.mul_mod]
            ring_nf
            simp [Nat.dvd_refl]
    · constructor
      · exact ModMul_valid _ _ _
      · rw [ModMul_spec, ModMul_spec, spec_temp]
        rw [← hn]
        have mod_one : n % 2 = 1 := by
          rw [← hn] at heven
          cases Nat.mod_two_eq_zero_or_one n <;> simp [*] at heven
        have : n = 2 * (n / 2) + 1 := by
          rw [← Nat.div_add_mod n 2, mod_one]
        rw [this]
        clear this
        generalize hk : n / 2 = k
        rw [← hk] at spec_temp
        simp [Exp_int]
        by_cases hz : k = 0
        · simp [hz, Exp_int]
          ring_nf
          rw [Nat.mod_mod_of_dvd]
          simp [Nat.dvd_refl]
        · rw [Exp_int]
          split_ifs
          · contradiction
          · simp [Nat.pow_succ]
            ring_nf
            rw [Nat.mul_mod, Nat.mul_mod, Nat.mod_mod_of_dvd, ← Nat.mul_mod, ← Nat.mul_mod]
            ring_nf
            simp [Nat.dvd_refl]
-- </vc-proof>

end BignumLean