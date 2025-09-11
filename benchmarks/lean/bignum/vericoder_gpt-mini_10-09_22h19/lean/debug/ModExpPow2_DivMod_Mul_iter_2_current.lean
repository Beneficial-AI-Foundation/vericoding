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

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

-- <vc-helpers>
-- LLM HELPER
lemma valid_one : BignumLean.ValidBitString "1" := by
  intro i c h
  cases i with
  | zero =>
    simp at h
    injection h with hc
    subst hc
    left
    rfl
  | succ _ =>
    simp at h
    contradiction

-- LLM HELPER
lemma exp_double (x m : Nat) : BignumLean.Exp_int x (2 * m) = BignumLean.Exp_int x m * BignumLean.Exp_int x m := by
  induction m with
  | zero =>
    simp [BignumLean.Exp_int]
  | succ m ih =>
    simp [BignumLean.Exp_int]
    -- 2 * (m + 1) = (2 * m) + 2
    have : 2 * (m + 1) = (2 * m) + 2 := by
      simp [Nat.add_comm, Nat.mul_succ, Nat.mul_comm]
    rw [this]
    -- Exp_int x ((2*m)+2) = x * Exp_int x ((2*m)+1) = x * (x * Exp_int x (2*m)) = (x * x) * Exp_int x (2*m)
    calc
      BignumLean.Exp_int x ((2 * m) + 2)
        = x * BignumLean.Exp_int x ((2 * m) + 1) := by simp [BignumLean.Exp_int]
      _ = x * (x * BignumLean.Exp_int x (2 * m)) := by simp [BignumLean.Exp_int]
      _ = (x * x) * BignumLean.Exp_int x (2 * m) := by ring
      _ = (x * x) * (BignumLean.Exp_int x m * BignumLean.Exp_int x m) := by rw [ih]
      _ = (x * BignumLean.Exp_int x m) * (x * BignumLean.Exp_int x m) := by ring
      _ = BignumLean.Exp_int x (m + 1) * BignumLean.Exp_int x (m + 1) := by simp [BignumLean.Exp_int]

-- LLM HELPER
lemma exp_mod_congr {a b t m : Nat} (h : a % m = b % m) : (BignumLean.Exp_int a t) % m = (BignumLean.Exp_int b t) % m := by
  induction t with
  | zero => simp [BignumLean.Exp_int]
  | succ t ih =>
    simp [BignumLean.Exp_int]
    -- (a * A) % m = ((a % m) * (A % m)) % m, similarly for b
    have hm1 : (a * BignumLean.Exp_int a t) % m = ((a % m) * (BignumLean.Exp_int a t % m)) % m := by
      apply (Nat.mul_mod _ _ m).symm
    have hm2 : (b * BignumLean.Exp_int b t) % m = ((b % m) * (BignumLean.Exp_int b t % m)) % m := by
      apply (Nat.mul_mod _ _ m).symm
    rw [hm1, hm2]
    rw [h, ih]

-- LLM HELPER
lemma exp_pow_square (a t : Nat) : BignumLean.Exp_int (a * a) t = BignumLean.Exp_int a (2 * t) := by
  induction t with
  | zero => simp [BignumLean.Exp_int]
  | succ t ih =>
    simp [BignumLean.Exp_int]
    -- LHS = (a*a) * Exp_int (a*a) t
    -- By IH Exp_int (a*a) t = Exp_int a (2*t)
    rw [ih]
    -- So LHS = (a*a) * Exp_int a (2*t)
    -- RHS = Exp_int a (2 *
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
lemma valid_one : BignumLean.ValidBitString "1" := by
  intro i c h
  cases i with
  | zero =>
    simp at h
    injection h with hc
    subst hc
    left
    rfl
  | succ _ =>
    simp at h
    contradiction

-- LLM HELPER
lemma exp_double (x m : Nat) : BignumLean.Exp_int x (2 * m) = BignumLean.Exp_int x m * BignumLean.Exp_int x m := by
  induction m with
  | zero =>
    simp [BignumLean.Exp_int]
  | succ m ih =>
    simp [BignumLean.Exp_int]
    -- 2 * (m + 1) = (2 * m) + 2
    have : 2 * (m + 1) = (2 * m) + 2 := by
      simp [Nat.add_comm, Nat.mul_succ, Nat.mul_comm]
    rw [this]
    -- Exp_int x ((2*m)+2) = x * Exp_int x ((2*m)+1) = x * (x * Exp_int x (2*m)) = (x * x) * Exp_int x (2*m)
    calc
      BignumLean.Exp_int x ((2 * m) + 2)
        = x * BignumLean.Exp_int x ((2 * m) + 1) := by simp [BignumLean.Exp_int]
      _ = x * (x * BignumLean.Exp_int x (2 * m)) := by simp [BignumLean.Exp_int]
      _ = (x * x) * BignumLean.Exp_int x (2 * m) := by ring
      _ = (x * x) * (BignumLean.Exp_int x m * BignumLean.Exp_int x m) := by rw [ih]
      _ = (x * BignumLean.Exp_int x m) * (x * BignumLean.Exp_int x m) := by ring
      _ = BignumLean.Exp_int x (m + 1) * BignumLean.Exp_int x (m + 1) := by simp [BignumLean.Exp_int]

-- LLM HELPER
lemma exp_mod_congr {a b t m : Nat} (h : a % m = b % m) : (BignumLean.Exp_int a t) % m = (BignumLean.Exp_int b t) % m := by
  induction t with
  | zero => simp [BignumLean.Exp_int]
  | succ t ih =>
    simp [BignumLean.Exp_int]
    -- (a * A) % m = ((a % m) * (A % m)) % m, similarly for b
    have hm1 : (a * BignumLean.Exp_int a t) % m = ((a % m) * (BignumLean.Exp_int a t % m)) % m := by
      apply (Nat.mul_mod _ _ m).symm
    have hm2 : (b * BignumLean.Exp_int b t) % m = ((b % m) * (BignumLean.Exp_int b t % m)) % m := by
      apply (Nat.mul_mod _ _ m).symm
    rw [hm1, hm2]
    rw [h, ih]

-- LLM HELPER
lemma exp_pow_square (a t : Nat) : BignumLean.Exp_int (a * a) t = BignumLean.Exp_int a (2 * t) := by
  induction t with
  | zero => simp [BignumLean.Exp_int]
  | succ t ih =>
    simp [BignumLean.Exp_int]
    -- LHS = (a*a) * Exp_int (a*a) t
    -- By IH Exp_int (a*a) t = Exp_int a (2*t)
    rw [ih]
    -- So LHS = (a*a) * Exp_int a (2*t)
    -- RHS = Exp_int a (2 *
-- </vc-code>

end BignumLean