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

def DivMod (dividend divisor : String) : (String × String) :=
  sorry

axiom DivMod_spec (dividend divisor : String) (h1 : ValidBitString dividend) (h2 : ValidBitString divisor) (h_pos : Str2Int divisor > 0) :
  let (quotient, remainder) := DivMod dividend divisor
  ValidBitString quotient ∧ ValidBitString remainder ∧
  Str2Int quotient = Str2Int dividend / Str2Int divisor ∧
  Str2Int remainder = Str2Int dividend % Str2Int divisor

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

-- <vc-helpers>
-- LLM HELPER
def ModExpPow2Helper (sx : String) (n : Nat) (sz : String) : String :=
  if n = 0 then
    let (_, r) := DivMod sx sz
    r  -- x^1 mod z
  else
    let half := ModExpPow2Helper sx (n - 1) sz
    let squared := Mul half half
    let (_, result) := DivMod squared sz
    result

-- LLM HELPER
theorem ModExpPow2Helper_spec (sx : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hz : ValidBitString sz) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2Helper sx n sz) ∧
  Str2Int (ModExpPow2Helper sx n sz) = Exp_int (Str2Int sx) (Exp_int 2 n) % Str2Int sz := by
  induction n generalizing sx with
  | zero =>
    simp only [ModExpPow2Helper]
    simp only [Exp_int]
    have hsz_pos : Str2Int sz > 0 := Nat.zero_lt_of_lt hsz_gt1
    have div_spec := DivMod_spec sx sz hx hz hsz_pos
    obtain ⟨_, hr, _, hr_val⟩ := div_spec
    exact ⟨hr, hr_val⟩
  | succ n' ih =>
    simp only [ModExpPow2Helper]
    have ih_result := ih
    obtain ⟨h_valid_half, h_val_half⟩ := ih_result
    have mul_spec := Mul_spec (ModExpPow2Helper sx n' sz) (ModExpPow2Helper sx n' sz) h_valid_half h_valid_half
    obtain ⟨h_valid_squared, h_val_squared⟩ := mul_spec
    rw [h_val_half] at h_val_squared
    have hsz_pos : Str2Int sz > 0 := Nat.zero_lt_of_lt hsz_gt1
    have div_spec := DivMod_spec (Mul (ModExpPow2Helper sx n' sz) (ModExpPow2Helper sx n' sz)) sz h_valid_squared hz hsz_pos
    obtain ⟨_, hr, _, hr_val⟩ := div_spec
    constructor
    · exact hr
    · rw [hr_val, h_val_squared]
      simp only [Exp_int]
      have exp_succ : Exp_int 2 (n' + 1) = 2 * Exp_int 2 n' := by
        simp only [Exp_int]
        split
        · omega
        · congr 1
          omega
      rw [exp_succ]
      have mod_mul : ∀ a b c : Nat, c > 0 → (a % c * b % c) % c = (a * b) % c := by
        intros a b c hc
        rw [Nat.mul_mod, Nat.mod_mod_of_dvd, Nat.mul_mod]
        · exact hc
        · exact hc
      rw [← mod_mul _ _ _ hsz_pos]
      congr 1
      have exp_double : Exp_int (Str2Int sx) (2 * Exp_int 2 n') = 
                       Exp_int (Str2Int sx) (Exp_int 2 n') * Exp_int (Str2Int sx) (Exp_int 2 n') := by
        generalize hx_val : Str2Int sx = x
        generalize hn_val : Exp_int 2 n' = m
        clear ih ih_result h_valid_half h_val_half mul_spec h_valid_squared h_val_squared div_spec hr hr_val hx_val hn_val
        induction m with
        | zero => simp only [Exp_int, Nat.mul_zero]
        | succ m' ih => 
          simp only [Exp_int, Nat.mul_succ]
          rw [← ih]
          ring
      exact exp_double
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if Str2Int sy = 0 then
    "1"  -- x^0 = 1
  else
    -- sy = 2^n case
    ModExpPow2Helper sx n sz
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
  rcases hsy_pow2 with h_pow2 | h_zero
  · -- Case: sy = 2^n
    simp only [h_pow2]
    have h_ne_zero : Exp_int 2 n ≠ 0 := by
      induction n with
      | zero => simp only [Exp_int]
      | succ n' _ => simp only [Exp_int]; omega
    simp only [h_ne_zero, ite_false]
    rw [h_pow2]
    exact ModExpPow2Helper_spec sx n sz hx hz hsz_gt1
  · -- Case: sy = 0
    simp only [h_zero, Exp_int, ite_true]
    constructor
    · unfold ValidBitString
      intros i c h_get
      simp only at h_get
      cases i with
      | zero => simp only at h_get; left; exact h_get
      | succ _ => simp only at h_get
    · simp only [Str2Int]
      exact Nat.mod_eq_of_lt hsz_gt1
-- </vc-proof>

end BignumLean