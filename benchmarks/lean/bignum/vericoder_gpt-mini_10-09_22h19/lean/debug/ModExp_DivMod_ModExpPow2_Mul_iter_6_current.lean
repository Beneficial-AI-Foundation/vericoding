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

def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  sorry

axiom ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

-- <vc-helpers>
-- LLM HELPER
theorem Exp_int_add (x m n : Nat) : Exp_int x (m + n) = Exp_int x m * Exp_int x n := by
  induction n with
  | zero => simp [Exp_int, Nat.zero_add]
  | succ n ih =>
    calc
      Exp_int x (m + n.succ) = Exp_int x (m + n).succ := rfl
      _ = x * Exp_int x (m + n) := by simp [Exp_int]
      _ = x * (Exp_int x m * Exp_int x n) := by rw [ih]
      _ = (x * Exp_int x m) * Exp_int x n := by simp [mul_assoc]
      _ = Exp_int x m.succ * Exp_int x n := by simp [Exp_int]
      _ = Exp_int x m * Exp_int x n.succ := by
        -- adjust form to match goal; actually we want Exp_int x (m + n.succ) = Exp_int x m * Exp_int x n.succ
        -- but the previous lines already show equality to x * Exp_int x (m + n), which equals Exp_int x m * Exp_int x n.succ
        rfl

-- LLM HELPER
theorem mul_mod_eq (x y m : Nat) : (x * y) % m = ((x % m) * (y % m)) % m := by
  have hx := Nat.div_add_mod x m
  have hy := Nat.div_add_mod y m
  -- x = (x/m)*m + x%m, y = (y/m)*m + y%m
  have : x * y = ((x / m) * m + x % m) * ((y / m) * m + y % m) := by
    rw [hx, hy]
  rw [this]
  -- expand and reduce modulo m
  simp only [mul_add, add_mul, mul_comm _ (x % m), mul_comm _ (y % m), mul_assoc]
  -- all terms except (x % m) * (y % m) are multiples of m
  have : ((x / m) * m) * ((y / m) * m) + ((x / m) * m) * (y % m) + (x % m) * ((y / m) * m) =
          m * (((x / m) * (y / m) * m) + (x / m) * (y % m) + (x % m) * (y / m)) := by
    ring
  rw [this]
  simp [Nat.add_comm]
  -- Now mod m both sides
  have : (m * (((x / m) * (y / m) * m) + (x / m) * (y % m) + (x % m) * (y / m)) + (x % m) * (y % m)) % m
         = ((x % m) * (y % m)) % m := by
    apply congrArg
    apply Eq.refl
  -- combine to get the result
  have final := by
    rw [Nat.add_comm] at this
    exact this
  exact final

-- LLM HELPER
theorem Exp_int_two_mul (x n : Nat) : Exp_int x (2 * n) = Exp_int x n * Exp_int x n := by
  calc
    Exp_int x (2 * n) = Exp_int x (n + n) := by simp
    _ = Exp_int x n * Exp_int x n := by apply Exp_int_add

-- LLM HELPER
/-
  General invariant lemma for the left-to-right binary modular exponentiation fold.

  step r ch :=
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
theorem Exp_int_add (x m n : Nat) : Exp_int x (m + n) = Exp_int x m * Exp_int x n := by
  induction n with
  | zero => simp [Exp_int, Nat.zero_add]
  | succ n ih =>
    calc
      Exp_int x (m + n.succ) = Exp_int x (m + n).succ := rfl
      _ = x * Exp_int x (m + n) := by simp [Exp_int]
      _ = x * (Exp_int x m * Exp_int x n) := by rw [ih]
      _ = (x * Exp_int x m) * Exp_int x n := by simp [mul_assoc]
      _ = Exp_int x m.succ * Exp_int x n := by simp [Exp_int]
      _ = Exp_int x m * Exp_int x n.succ := by
        -- adjust form to match goal; actually we want Exp_int x (m + n.succ) = Exp_int x m * Exp_int x n.succ
        -- but the previous lines already show equality to x * Exp_int x (m + n), which equals Exp_int x m * Exp_int x n.succ
        rfl

-- LLM HELPER
theorem mul_mod_eq (x y m : Nat) : (x * y) % m = ((x % m) * (y % m)) % m := by
  have hx := Nat.div_add_mod x m
  have hy := Nat.div_add_mod y m
  -- x = (x/m)*m + x%m, y = (y/m)*m + y%m
  have : x * y = ((x / m) * m + x % m) * ((y / m) * m + y % m) := by
    rw [hx, hy]
  rw [this]
  -- expand and reduce modulo m
  simp only [mul_add, add_mul, mul_comm _ (x % m), mul_comm _ (y % m), mul_assoc]
  -- all terms except (x % m) * (y % m) are multiples of m
  have : ((x / m) * m) * ((y / m) * m) + ((x / m) * m) * (y % m) + (x % m) * ((y / m) * m) =
          m * (((x / m) * (y / m) * m) + (x / m) * (y % m) + (x % m) * (y / m)) := by
    ring
  rw [this]
  simp [Nat.add_comm]
  -- Now mod m both sides
  have : (m * (((x / m) * (y / m) * m) + (x / m) * (y % m) + (x % m) * (y / m)) + (x % m) * (y % m)) % m
         = ((x % m) * (y % m)) % m := by
    apply congrArg
    apply Eq.refl
  -- combine to get the result
  have final := by
    rw [Nat.add_comm] at this
    exact this
  exact final

-- LLM HELPER
theorem Exp_int_two_mul (x n : Nat) : Exp_int x (2 * n) = Exp_int x n * Exp_int x n := by
  calc
    Exp_int x (2 * n) = Exp_int x (n + n) := by simp
    _ = Exp_int x n * Exp_int x n := by apply Exp_int_add

-- LLM HELPER
/-
  General invariant lemma for the left-to-right binary modular exponentiation fold.

  step r ch :=
-- </vc-code>

end BignumLean