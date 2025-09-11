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
theorem Exp_int_add (x a b : Nat) : Exp_int x (a + b) = Exp_int x a * Exp_int x b := by
  -- Induction on b, generalizing a so we can increment the right summand
  induction b generalizing a with
  | zero =>
    -- a + 0 = a and Exp_int x 0 = 1, so both sides reduce to Exp_int x a
    rw [Nat.add_zero]
    have h0 : Exp_int x 0 = 1 := by
      dsimp [Exp_int]; rfl
    simp [h0]
  | succ b ih =>
    -- (a + b) + 1 = a + (b + 1)
    calc
      Exp_int x (a + b + 1) = x * Exp_int x (a + b) := by
        -- by definition since (a + b + 1) ≠ 0
        dsimp [Exp_int]; split_ifs with H; 
        · contradiction
        · rfl
      _ = x * (Exp_int x a * Exp_int x b) := by rw [ih]
      _ = (Exp_int x a) * (x * Exp_int x b) := by
        -- use commutativity/associativity from Nat
        rw [Nat.mul_comm (Exp_int x a) (x * Exp_int x b)]
        rfl

-- LLM HELPER
theorem Exp
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
theorem Exp_int_add (x a b : Nat) : Exp_int x (a + b) = Exp_int x a * Exp_int x b := by
  -- Induction on b, generalizing a so we can increment the right summand
  induction b generalizing a with
  | zero =>
    -- a + 0 = a and Exp_int x 0 = 1, so both sides reduce to Exp_int x a
    rw [Nat.add_zero]
    have h0 : Exp_int x 0 = 1 := by
      dsimp [Exp_int]; rfl
    simp [h0]
  | succ b ih =>
    -- (a + b) + 1 = a + (b + 1)
    calc
      Exp_int x (a + b + 1) = x * Exp_int x (a + b) := by
        -- by definition since (a + b + 1) ≠ 0
        dsimp [Exp_int]; split_ifs with H; 
        · contradiction
        · rfl
      _ = x * (Exp_int x a * Exp_int x b) := by rw [ih]
      _ = (Exp_int x a) * (x * Exp_int x b) := by
        -- use commutativity/associativity from Nat
        rw [Nat.mul_comm (Exp_int x a) (x * Exp_int x b)]
        rfl

-- LLM HELPER
theorem Exp
-- </vc-code>

end BignumLean