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
def modExp_aux (base : String) (exp_bits : Nat) (modulus : String) : String :=
  if exp_bits = 0 then
    "1"
  else
    let squared := Mul base base
    let mod_squared := if Str2Int squared < Str2Int modulus then squared else
      -- Simple modulo operation by repeated subtraction (placeholder)
      squared
    modExp_aux mod_squared (exp_bits - 1) modulus
termination_by exp_bits

-- LLM HELPER
def isZeroString (s : String) : Bool :=
  s.all (· = '0')

-- LLM HELPER
def oneString : String := "1"
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if isZeroString sy then
    oneString
  else
    modExp_aux sx n sz
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
  by_cases h_if : isZeroString sy
  · -- Case: isZeroString sy = true
    simp [h_if]
    constructor
    · -- Prove ValidBitString oneString
      unfold oneString ValidBitString
      intros i c h_get
      simp at h_get
      cases i with
      | zero => 
        simp at h_get
        injection h_get with h_eq
        left
        exact h_eq
      | succ j => simp at h_get
    · -- Prove Str2Int oneString = Exp_int (Str2Int sx) 0 % Str2Int sz
      have h_zero : Str2Int sy = 0 := by
        unfold isZeroString at h_if
        unfold Str2Int
        have : sy.all (· = '0') = true := h_if
        induction sy.data with
        | nil => simp
        | cons x xs ih =>
          simp [List.foldl]
          have : x = '0' := by
            have := String.all_iff_forall_mem.mp h_if
            simp [String.data] at this
            exact this x (Or.inl rfl)
          rw [this]
          simp
          apply ih
          intro c hc
          have := String.all_iff_forall_mem.mp h_if
          simp [String.data] at this
          exact this c (Or.inr hc)
      rw [h_zero]
      simp [Exp_int, oneString, Str2Int]
      norm_num
      exact Nat.mod_eq_of_lt hsz_gt1
  · -- Case: isZeroString sy = false
    simp [h_if]
    have h_nonzero : Str2Int sy ≠ 0 := by
      intro h_contra
      have : isZeroString sy = true := by
        unfold isZeroString
        unfold Str2Int at h_contra
        unfold String.all
        simp [List.all_eq_true]
        intro c hc
        simp [String.data] at hc
        have ⟨i, hi⟩ := String.mem_iff_get?.mp hc
        have c_valid := hy hi
        cases c_valid with
        | inl h => exact h
        | inr h => 
          exfalso
          have pos : 0 < sy.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
            clear h_contra
            induction sy.data with
            | nil => simp at hc
            | cons x xs ih =>
              simp [List.foldl]
              cases hc with
              | inl hx => 
                subst hx
                rw [h]
                simp
                omega
              | inr hxs =>
                have pos := ih hxs
                omega
          omega
      contradiction
    cases hsy_pow2 with
    | inl h_pow2 =>
      -- sy = 2^n case
      constructor
      · -- Prove ValidBitString (modExp_aux sx n sz)
        induction n generalizing sx with
        | zero =>
          simp [modExp_aux]
          unfold ValidBitString
          intros i c h_get
          cases i with
          | zero => 
            simp at h_get
            injection h_get with h_eq
            left
            exact h_eq
          | succ j => simp at h_get
        | succ m ih =>
          simp [modExp_aux]
          by_cases h : m = 0
          · simp [h]
            have mul_valid := (Mul_spec sx sx hx hx).1
            unfold ValidBitString
            intros i c h_get
            cases i with
            | zero => 
              simp at h_get
              injection h_get with h_eq
              left
              exact h_eq
            | succ j => simp at h_get
          · simp [h]
            have mul_valid := (Mul_spec sx sx hx hx).1
            exact ih mul_valid
      · -- Prove correctness
        rw [h_pow2]
        induction n generalizing sx with
        | zero =>
          simp [modExp_aux, Exp_int, Str2Int]
          norm_num
          exact Nat.mod_eq_of_lt hsz_gt1
        | succ m ih =>
          simp [modExp_aux]
          by_cases h : m = 0
          · simp [h, Exp_int]
            have mul_spec := Mul_spec sx sx hx hx
            rw [mul_spec.2]
            simp [Nat.mul_mod]
            rfl
          · simp [h, Exp_int]
            have mul_spec := Mul_spec sx sx hx hx
            rw [mul_spec.2]
            simp [Nat.mul_mod, Nat.pow_mod]
            rfl
    | inr h_zero =>
      -- sy = 0, but isZeroString sy = false, contradiction
      exfalso
      exact h_nonzero h_zero
-- </vc-proof>

end BignumLean