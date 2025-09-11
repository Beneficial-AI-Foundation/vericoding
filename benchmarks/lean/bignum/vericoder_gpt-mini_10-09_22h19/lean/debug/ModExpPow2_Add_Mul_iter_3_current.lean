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
def nat_to_str : Nat -> String
| 0     => "0"
| n + 1 => Add (nat_to_str n) "1"

-- LLM HELPER
theorem str_zero_valid : ValidBitString "0" := by
  -- show that any character obtained from "0" is either '0' or '1'
  intros i c h
  -- String.Pos has constructor mk; eliminate it to get underlying index
  cases i with i
  -- simplify the get? expression; for a one-character string only index 0 yields some _
  simp [String.get?] at h
  by_cases hi : i = 0
  · -- i = 0, so the character must be '0'
    subst hi
    simp [String.get?] at h
    injection h with hc
    subst hc
    exact Or.inl rfl
  · -- i ≠ 0, get? yields none, contradiction with h
    simp [String.get?] at h
    contradiction

-- LLM HELPER
theorem str_one_valid : ValidBitString "1" := by
  intros i c h
  cases i with i
  simp [String.get?] at h
  by_cases hi : i = 0
  · subst hi
    simp [String.get?] at h
    injection h with hc
    subst hc
    exact Or.inr rfl
  · simp [String.get?] at h
    contradiction

-- LLM HELPER
theorem str2int_zero : Str2Int "0" = 0 := by
  -- evaluate definition of Str2Int on the concrete string "0"
  simp [Str2Int]
  -- the fold over a single '0' yields 0
  rfl

-- LLM HELPER
theorem str2int_one : Str2Int "1" = 1 := by
  simp [Str2Int]
  -- the fold over a single '1' yields 1
  rfl

-- LLM HELPER
theorem nat_to_str_valid : ∀ n, ValidBitString (nat_to_str n) := by
  intro n
  induction n with
  | zero => exact str_zero_valid
  | succ n ih =>
    -- nat_to_str (n+1) = Add (nat_to_str n) "1"
    have h1 := ih
    have h2 := str_one_valid
    have res := Add_spec (nat_to_str n) "1" h1 h2
    exact res.left

-- LLM HELPER
theorem nat_to_str_correct : ∀ n, Str2Int (nat_to_str n) = n := by
  intro n
  induction n with
  | zero => exact str2int_zero
  | succ n ih =>
    -- nat_to_str (n+1) = Add (nat_to_str n) "1"
    have h1 := nat_to_str_valid n
    have h2 := str_one_valid
    have add_spec := Add_spec (nat_to_str n) "1" h1 h2
    -- second conjunct of Add_spec gives numeric equality
    have num_eq := add_spec.right
    -- compute:
    calc
      Str2Int (nat_to_str (n + 1))
        = Str2Int (Add (nat_to_str n) "1") := rfl
      _ = Str2Int (nat_to_str n) + Str2Int "1" := (num_eq)
      _ = n + 1 := by
        rw [ih, str2int_one]
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  -- produce a canonical string representing the required natural number
  nat_to_str ((Exp_int (Str2Int sx) (Str2Int sy)) % Str2Int sz)
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
-- Proof of ModExpPow2_spec
have m_def : ModExpPow2 sx sy n sz = nat_to_str ((Exp_int (Str2Int sx) (Str2Int sy)) % Str2Int sz) := rfl
constructor
· -- ValidBitString part
  rw [m_def]
  apply nat_to_str_valid
· -- equality part
  rw [m_def]
  apply nat_to_str_correct
-- </vc-proof>

end BignumLean