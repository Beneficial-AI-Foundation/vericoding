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
  sorry

-- LLM HELPER  
lemma Str2Int_Nat2Str (n : Nat) : Str2Int (Nat2Str n) = n := by
  sorry

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
  have h1 : sy ≠ "0" := by assumption
  have h2 : sy ≠ "1" := by assumption
  have : Str2Int sy ≠ 0 := by
    intro h
    have : sy = "0" ∨ sy.data = [] := by
      unfold Str2Int at h
      cases sy.data with
      | nil => right; rfl
      | cons c cs =>
        simp at h
        left; ext; simp; exact h
    cases this with
    | inl h => exact h1 h
    | inr h => 
      have : Str2Int sy = 0 := by unfold Str2Int; simp [h]
      contradiction
  have : Str2Int sy ≠ 1 := by
    intro h
    unfold Str2Int at h
    cases hd : sy.data with
    | nil => simp [hd] at h
    | cons c cs =>
      simp at h
      have : sy = "1" := by
        ext
        simp [hd]
        cases h with
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
      exact h2 this
  have pos : 0 < Str2Int sy := Nat.zero_lt_of_ne_zero this
  have gt_one : 1 < Str2Int sy := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨this, ‹Str2Int sy ≠ 1›⟩
  exact Nat.div_lt_self pos (by norm_num : 1 < 2)
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
sorry
-- </vc-proof>

end BignumLean