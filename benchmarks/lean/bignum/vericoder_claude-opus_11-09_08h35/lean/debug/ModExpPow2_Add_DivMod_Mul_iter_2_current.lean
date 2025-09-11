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
  match n with
  | 0 => "1"
  | n' + 1 => 
    let squared := Mul sx sx
    let (_, remainder) := DivMod squared sz
    ModExpPow2Helper remainder n' sz

-- LLM HELPER
lemma ModExpPow2Helper_spec (sx : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hz : ValidBitString sz) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2Helper sx n sz) ∧
  Str2Int (ModExpPow2Helper sx n sz) = Exp_int (Str2Int sx) (Exp_int 2 n) % Str2Int sz := by
  induction n generalizing sx with
  | zero =>
    simp [ModExpPow2Helper, Exp_int]
    constructor
    · unfold ValidBitString
      intros i c h_get
      simp at h_get
      cases i with
      | zero => simp at h_get; left; exact h_get
      | succ _ => simp at h_get
    · simp [Str2Int]
      exact Nat.mod_eq_of_lt hsz_gt1
  | succ n' ih =>
    simp [ModExpPow2Helper]
    have mul_valid := Mul_spec sx sx hx hx
    have div_spec := DivMod_spec (Mul sx sx) sz mul_valid.1 hz hsz_gt1
    let squared := Mul sx sx
    let divmod_result := DivMod squared sz
    have remainder_valid := div_spec.2.1
    have remainder_value := div_spec.2.2.2
    have ih_result := ih divmod_result.2 remainder_valid
    constructor
    · exact ih_result.1
    · rw [ih_result.2, remainder_value, mul_valid.2]
      simp [Exp_int]
      have h_pow : Exp_int 2 (n' + 1) = 2 * Exp_int 2 n' := by simp [Exp_int]
      rw [h_pow]
      have h_exp : Exp_int (Str2Int sx) (2 * Exp_int 2 n') = 
                   Exp_int (Exp_int (Str2Int sx) 2) (Exp_int 2 n') := by
        clear ih_result remainder_value div_spec mul_valid
        generalize Str2Int sx = x
        generalize Exp_int 2 n' = m
        induction m with
        | zero => simp [Exp_int]
        | succ m' ihm =>
          simp [Exp_int, Nat.mul_succ]
          rw [← ihm]
          simp [Exp_int]
          ring
      rw [h_exp]
      simp [Exp_int]
      rw [Nat.mul_mod, Nat.mod_mod_of_dvd, Nat.mod_mul_mod]
      · rfl
      · exact Nat.zero_lt_of_lt hsz_gt1
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
  cases hsy_pow2 with
  | inl h_pow2 =>
    -- Case: sy = 2^n
    simp [h_pow2]
    have h_ne_zero : Exp_int 2 n ≠ 0 := by
      induction n with
      | zero => simp [Exp_int]
      | succ n' _ => simp [Exp_int]; omega
    simp [h_ne_zero]
    rw [h_pow2]
    exact ModExpPow2Helper_spec sx n sz hx hz hsz_gt1
  | inr h_zero =>
    -- Case: sy = 0
    simp [h_zero, Exp_int]
    constructor
    · unfold ValidBitString
      intros i c h_get
      simp at h_get
      cases i with
      | zero => simp at h_get; left; exact h_get
      | succ _ => simp at h_get
    · simp [Str2Int]
      exact Nat.mod_eq_of_lt hsz_gt1
-- </vc-proof>

end BignumLean