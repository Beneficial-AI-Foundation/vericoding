namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Add (s1 s2 : String) : String :=
  sorry

axiom Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2

def NormalizeBitString (s : String) : String :=
  sorry

axiom NormalizeBitString_spec (s : String) :
  ValidBitString (NormalizeBitString s) ∧
  (NormalizeBitString s).length > 0 ∧
  ((NormalizeBitString s).length > 1 → (NormalizeBitString s).get? 0 = some '1') ∧
  (ValidBitString s → Str2Int s = Str2Int (NormalizeBitString s))

-- <vc-helpers>
-- LLM HELPER
def char_to_bit (c : Char) : Nat := if c = '1' then 1 else 0

-- LLM HELPER
def bit_to_char (b : Nat) : Char := if b = 1 then '1' else '0'

-- LLM HELPER
theorem str2int_zero : Str2Int "0" = 0 := by
  dsimp [Str2Int]
  have : "0".data = ['0'] := rfl
  rw [this]
  simp [List.foldl]

-- LLM HELPER
theorem valid_bits_bound {s : String} (h : ValidBitString s) :
  Str2Int s < (2 : Nat) ^ s.length := by
  induction s.data generalizing s with
  | nil =>
    dsimp [Str2Int]
    simp
  | cons c cs ih =>
    let s' := String.mk (c :: cs)
    dsimp [Str2Int] at *
    -- Str2Int (c :: cs) = 2 * Str2Int (String.mk cs) + bit
    have Hfld : Str2Int s' = 2 * Str2Int (String.mk cs) + (if c = '1' then 1 else 0) := rfl
    rw [Hfld]
    have ih' : Str2Int (String.mk cs) < 2 ^ cs.length := ih
    -- 2 * Str2Int cs <= 2 * (2^cs.length - 1) = 2^(cs.length+1) - 2
    calc
      2 * Str2Int (String.mk cs) + (if c = '1' then 1 else 0)
          ≤ 2 * (2 ^ cs.length - 1) + 1 := by
        have : Str2Int (String.mk cs) ≤ 2 ^ cs.length - 1 := by
          linarith [ih']
        calc
          2 * Str2Int (String.mk cs) + (if c = '1' then 1 else 0)
              ≤ 2 * (2 ^ cs.length - 1) + 1 := by
            apply Nat.add_le_add_left; exact (Nat.mul_le_mul_left _ this)
      _ = 2 ^ (cs.length + 1) - 1 := by
        simp [pow_succ]
      _ < 2 ^ (cs.length + 1) := by
        linarith
    -- conclusion: < 2^(s'.length)
-- </vc-helpers>

-- <vc-spec>
def Mul (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
def char_to_bit (c : Char) : Nat := if c = '1' then 1 else 0

-- LLM HELPER
def bit_to_char (b : Nat) : Char := if b = 1 then '1' else '0'

-- LLM HELPER
theorem str2int_zero : Str2Int "0" = 0 := by
  dsimp [Str2Int]
  have : "0".data = ['0'] := rfl
  rw [this]
  simp [List.foldl]

-- LLM HELPER
theorem valid_bits_bound {s : String} (h : ValidBitString s) :
  Str2Int s < (2 : Nat) ^ s.length := by
  induction s.data generalizing s with
  | nil =>
    dsimp [Str2Int]
    simp
  | cons c cs ih =>
    let s' := String.mk (c :: cs)
    dsimp [Str2Int] at *
    -- Str2Int (c :: cs) = 2 * Str2Int (String.mk cs) + bit
    have Hfld : Str2Int s' = 2 * Str2Int (String.mk cs) + (if c = '1' then 1 else 0) := rfl
    rw [Hfld]
    have ih' : Str2Int (String.mk cs) < 2 ^ cs.length := ih
    -- 2 * Str2Int cs <= 2 * (2^cs.length - 1) = 2^(cs.length+1) - 2
    calc
      2 * Str2Int (String.mk cs) + (if c = '1' then 1 else 0)
          ≤ 2 * (2 ^ cs.length - 1) + 1 := by
        have : Str2Int (String.mk cs) ≤ 2 ^ cs.length - 1 := by
          linarith [ih']
        calc
          2 * Str2Int (String.mk cs) + (if c = '1' then 1 else 0)
              ≤ 2 * (2 ^ cs.length - 1) + 1 := by
            apply Nat.add_le_add_left; exact (Nat.mul_le_mul_left _ this)
      _ = 2 ^ (cs.length + 1) - 1 := by
        simp [pow_succ]
      _ < 2 ^ (cs.length + 1) := by
        linarith
    -- conclusion: < 2^(s'.length)
-- </vc-code>

end BignumLean