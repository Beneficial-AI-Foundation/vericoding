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
def Nat2Str (n : Nat) : String :=
  if n = 0 then "0" else Nat2StrAux n
where
  Nat2StrAux (n : Nat) : String :=
    if n = 0 then "" else
      Nat2StrAux (n / 2) ++ (if n % 2 = 0 then "0" else "1")
  termination_by n

-- LLM HELPER
lemma Nat2Str_valid (n : Nat) : ValidBitString (Nat2Str n) := by
  unfold ValidBitString Nat2Str
  split
  · intros i c h
    simp at h
    cases h
    left; rfl
  · intros i c
    generalize hn : n = m
    rw [← hn]
    clear hn m
    induction n using Nat.strongInductionOn with
    | ind n ih =>
      simp [Nat2Str.Nat2StrAux]
      split
      · simp
      · intro h
        have : ∃ j s₁ s₂, String.get? (Nat2Str.Nat2StrAux (n / 2) ++ if n % 2 = 0 then "0" else "1") i = String.get? (s₁ ++ s₂) j ∧ 
                          s₁ = Nat2Str.Nat2StrAux (n / 2) ∧ s₂ = if n % 2 = 0 then "0" else "1" := by
          use i, Nat2Str.Nat2StrAux (n / 2), if n % 2 = 0 then "0" else "1"
          simp
        obtain ⟨j, s₁, s₂, hget, hs₁, hs₂⟩ := this
        rw [← hs₁, ← hs₂] at hget
        rw [hget] at h
        cases' (String.get?_append s₁ s₂ j) with hlt hge
        · have ih_apply := ih (n / 2) (Nat.div_lt_self (by omega) (by omega))
          unfold ValidBitString at ih_apply
          rw [← hs₁] at hlt
          exact ih_apply (hlt.trans h)
        · rw [← hs₂] at hge
          split at hge
          · simp at hge
            rw [hge] at h
            simp at h
            cases h
            left; assumption
          · simp at hge
            rw [hge] at h
            simp at h
            cases h
            right; assumption

-- LLM HELPER
lemma Str2Int_Nat2Str (n : Nat) : Str2Int (Nat2Str n) = n := by
  unfold Nat2Str
  split
  · simp [Str2Int]
  · generalize hn : n = m
    rw [← hn]
    clear hn m
    induction n using Nat.strongInductionOn with
    | ind n ih =>
      simp [Nat2Str.Nat2StrAux]
      split
      · omega
      · rename_i h
        simp [Str2Int]
        have div_lt : n / 2 < n := Nat.div_lt_self (by omega) (by omega)
        have ih_apply := ih (n / 2) div_lt
        unfold Nat2Str at ih_apply
        split at ih_apply
        · omega
        · rw [← ih_apply]
          simp [Str2Int]
          split
          · simp
            have : n = 2 * (n / 2) := by
              have h := Nat.div_add_mod n 2
              omega
            omega
          · simp
            have : n = 2 * (n / 2) + 1 := by
              have h := Nat.div_add_mod n 2
              omega
            omega

-- LLM HELPER
def modExpNat (base exp modulus : Nat) : Nat :=
  if modulus = 0 then 0
  else if exp = 0 then 1 % modulus
  else 
    let halfExp := modExpNat base (exp / 2) modulus
    let squared := (halfExp * halfExp) % modulus
    if exp % 2 = 0 then squared
    else (squared * base) % modulus
termination_by exp

-- LLM HELPER
lemma modExpNat_eq_Exp_int_mod (base exp modulus : Nat) (h : modulus > 0) :
  modExpNat base exp modulus = Exp_int base exp % modulus := by
  generalize hexp : exp = e
  rw [← hexp]
  clear hexp e
  induction exp using Nat.strongInductionOn with
  | ind exp ih =>
    unfold modExpNat Exp_int
    split
    · omega
    · split
      · simp
      · rename_i h_exp_pos
        have div_lt : exp / 2 < exp := Nat.div_lt_self h_exp_pos (by omega)
        have ih_apply := ih (exp / 2) div_lt
        rw [ih_apply]
        split
        · have : exp = 2 * (exp / 2) := by
            have h := Nat.div_add_mod exp 2
            omega
          rw [this]
          clear this
          generalize exp / 2 = k
          clear exp h_exp_pos div_lt ih ih_apply
          induction k with
          | zero => simp [Exp_int]
          | succ k ih =>
            simp [Exp_int]
            ring_nf
            rw [Nat.mul_mod, Nat.mul_mod, ← Nat.mul_mod, ← Nat.mul_mod]
            congr 1
            ring
        · have : exp = 2 * (exp / 2) + 1 := by
            have h := Nat.div_add_mod exp 2
            omega
          rw [this]
          clear this
          generalize exp / 2 = k
          clear exp h_exp_pos div_lt ih ih_apply
          simp [Exp_int]
          rw [Nat.mul_mod, Nat.mul_mod, ← Nat.mul_mod, Nat.mul_mod]
          congr 1
          induction k with
          | zero => simp [Exp_int]
          | succ k ih =>
            simp [Exp_int]
            ring_nf
            rw [Nat.mul_mod, Nat.mul_mod, ← Nat.mul_mod, ← Nat.mul_mod]
            congr 1
            ring
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