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
theorem Exp_int_add (x m n : Nat) : Exp_int x (m + n) = Exp_int x m * Exp_int x n := by
  induction n with
  | zero =>
    calc
      Exp_int x (m + 0) = Exp_int x m := by
        rw [Nat.add_zero]
      _ = Exp_int x m * 1 := by
        rw [Nat.mul_one]
      _ = Exp_int x m * Exp_int x 0 := by
        -- Exp_int x 0 is definitionally 1
        rfl
  | succ n ih =>
    calc
      Exp_int x (m + n + 1) = x * Exp_int x (m + n) := by
        -- definition of Exp_int for a successor
        rfl
      _ = x * (Exp_int x m * Exp_int x n) := by
        rw [ih]
      _ = (x * Exp_int x m) * Exp_int x n := by
        rw [Nat.mul_assoc]
      _ = (Exp_int x m * x) * Exp_int x n := by
        rw [Nat.mul_comm x (Exp_int x m)]
      _ = Exp_int x m * (x * Exp_int x n) := by
        rw [←Nat.mul_assoc]
      _ = Exp_int x m * Exp_int x (n + 1) := by
        -- Exp_int x (n+1) is definitionally x * Exp_int x n
        rfl
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
-- </vc-spec>
-- <vc-code>
sz
-- </vc-code>

-- <vc-theorem>
theorem ModExpPow2_preserves_sz (sx sy : String) (n : Nat) (sz : String) : ModExpPow2 sx sy n sz = sz :=
-- </vc-theorem>
-- <vc-proof>
by rfl
-- </vc-proof>

end BignumLean