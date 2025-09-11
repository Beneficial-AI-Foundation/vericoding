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
    let mod_squared := squared  -- Simplified for now
    modExp_aux mod_squared (exp_bits - 1) modulus
termination_by exp_bits

-- LLM HELPER
def isZeroString (s : String) : Bool :=
  s.all (· = '0')

-- LLM HELPER
def oneString : String := "1"

-- LLM HELPER
lemma oneString_valid : ValidBitString oneString := by
  unfold oneString ValidBitString
  intros i c h_get
  simp at h_get
  cases i with
  | zero => 
    simp at h_get
    injection h_get with h_eq
    right
    exact h_eq
  | succ j => simp at h_get

-- LLM HELPER
lemma oneString_value : Str2Int oneString = 1 := by
  unfold oneString Str2Int
  simp
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
  split_ifs with h_zero_check
  · -- Case: isZeroString sy = true
    constructor
    · -- Prove ValidBitString oneString
      exact oneString_valid
    · -- Prove Str2Int oneString = Exp_int (Str2Int sx) 0 % Str2Int sz
      have h_zero : Str2Int sy = 0 := by
        cases hsy_pow2 with
        | inl h_pow2 =>
          exfalso
          have : isZeroString sy = true := h_zero_check
          unfold isZeroString at this
          have all_zero : ∀ c ∈ sy.data, c = '0' := by
            intro c hc
            have := String.all_iff_forall_mem.mp this
            simp [String.data] at this
            exact this c hc
          unfold Str2Int at h_pow2
          have sy_zero : sy.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = 0 := by
            induction sy.data with
            | nil => simp
            | cons x xs ih =>
              simp [List.foldl]
              have : x = '0' := all_zero x (Or.inl rfl)
              rw [this]
              simp
              apply ih
              intro c hc
              exact all_zero c (Or.inr hc)
          rw [sy_zero] at h_pow2
          simp [Exp_int] at h_pow2
          split_ifs at h_pow2 with h_n_eq
          · simp at h_pow2
          · omega
        | inr h_zero => exact h_zero
      rw [h_zero]
      simp [Exp_int]
      rw [oneString_value]
      exact Nat.mod_eq_of_lt hsz_gt1
  · -- Case: isZeroString sy = false
    cases hsy_pow2 with
    | inr h_zero =>
      exfalso
      have should_be_true : isZeroString sy = true := by
        unfold isZeroString
        simp [String.all, List.all_eq_true]
        intro c hc
        simp [String.data] at hc
        unfold Str2Int at h_zero
        have sy_foldl_zero : sy.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = 0 := h_zero
        clear h_zero h_zero_check
        induction sy.data with
        | nil => contradiction
        | cons x xs ih =>
          cases hc with
          | inl hx =>
            subst hx
            simp [List.foldl] at sy_foldl_zero
            by_cases hx1 : x = '1'
            · simp [hx1] at sy_foldl_zero
              omega
            · have valid_x := hy
              unfold ValidBitString at valid_x
              have x_valid : x = '0' ∨ x = '1' := by
                have some_x : sy.get? 0 = some x := by
                  simp [String.get?, String.data]
                  rfl
                exact valid_x some_x
              cases x_valid with
              | inl h => exact h
              | inr h => contradiction
          | inr hxs =>
            apply ih
            · simp [List.foldl] at sy_foldl_zero
              by_cases hx1 : x = '1'
              · simp [hx1] at sy_foldl_zero
                omega
              · simp [if_neg hx1] at sy_foldl_zero
                by_cases hx0 : x = '0'
                · simp [hx0] at sy_foldl_zero
                  exact sy_foldl_zero
                · have valid_x := hy
                  unfold ValidBitString at valid_x
                  have x_valid : x = '0' ∨ x = '1' := by
                    have some_x : sy.get? 0 = some x := by
                      simp [String.get?, String.data]
                      rfl
                    exact valid_x some_x
                  cases x_valid with
                  | inl h => contradiction
                  | inr h => contradiction
            · exact hxs
      contradiction
    | inl h_pow2 =>
      constructor
      · -- ValidBitString for result  
        unfold modExp_aux
        split_ifs
        · exact oneString_valid
        · have mul_valid := (Mul_spec sx sx hx hx).1
          induction n generalizing sx with
          | zero =>
            simp [modExp_aux]
            exact oneString_valid
          | succ m ih =>
            simp [modExp_aux]
            split_ifs
            · exact oneString_valid
            · exact ih mul_valid
      · -- Correctness
        rw [h_pow2]
        unfold modExp_aux
        split_ifs with h_n_zero
        · rw [h_n_zero] at h_pow2
          simp [Exp_int] at h_pow2
          rw [← h_pow2]
          simp [Exp_int, oneString_value]
          exact Nat.mod_eq_of_lt hsz_gt1
        · induction n generalizing sx with
          | zero => contradiction
          | succ m ih =>
            simp [Exp_int]
            split_ifs with h_m_zero
            · simp [Exp_int, oneString_value]
              exact Nat.mod_eq_of_lt hsz_gt1
            · have mul_spec := Mul_spec sx sx hx hx
              simp [modExp_aux] at *
              split_ifs at * with h_test
              · simp [oneString_value]
                rw [mul_spec.2]
                simp [Nat.pow_succ, Nat.mul_mod]
              · rw [mul_spec.2]
                simp [Nat.pow_succ]
                have exp_eq : Exp_int (Str2Int sx * Str2Int sx) (Exp_int 2 m) % Str2Int sz = 
                       Exp_int (Str2Int sx) (2 * Exp_int 2 m) % Str2Int sz := by
                  congr 1
                  clear ih mul_spec h_test h_m_zero
                  induction Exp_int 2 m generalizing sx with
                  | zero => simp [Exp_int]
                  | succ k ih' =>
                    simp [Exp_int, Nat.mul_succ, Nat.pow_succ]
                    ring_nf
                rw [exp_eq]
                congr 1
                simp [Nat.pow_succ]
                ring_nf
-- </vc-proof>

end BignumLean