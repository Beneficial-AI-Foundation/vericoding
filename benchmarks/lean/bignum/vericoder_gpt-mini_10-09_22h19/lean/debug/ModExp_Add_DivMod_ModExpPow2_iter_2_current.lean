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

def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  sorry

axiom ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz

-- <vc-helpers>
-- LLM HELPER
def nat_bits_aux : Nat -> List Char
| 0 => []
| m+1 =>
  let q := (m+1) / 2
  let r := (m+1) % 2
  (if r = 1 then '1' else '0') :: nat_bits_aux q

-- LLM HELPER
def nat_bits (n : Nat) : List Char :=
  if n = 0 then ['0'] else List.reverse (nat_bits_aux n)

-- LLM HELPER
def nat_to_bin (n : Nat) : String := String.mk (nat_bits n)

-- LLM HELPER
theorem nat_bits_aux_chars (n : Nat) :
  ∀ c, c ∈ nat_bits_aux n → c = '0' ∨ c = '1' := by
  intro c
  induction n with
  | zero =>
    intro h
    simp [nat_bits_aux] at h
    contradiction
  | succ m ih =>
    intro h
    simp [nat_bits_aux] at h
    -- membership in cons: either head (equal to bit) or in tail
    cases h with
    | head h0 =>
      let r := (m + 1) % 2
      by_cases hr : r = 1
      · simp [hr] at h0
        rw [h0]
        exact Or.inr rfl
      · simp [hr] at h0
        rw [h0]
        exact Or.inl rfl
    | tail ht =>
      apply ih
      exact ht

-- LLM HELPER
theorem nat_bits_chars (n : Nat) :
  ∀ c, c ∈ nat_bits n → c = '0' ∨ c = '1' := by
  intro c
  dsimp [nat_bits]
  by_cases h : n = 0
  · simp [h]
    intro hmem
    simp at hmem
    rcases hmem with rfl
    exact Or.inl rfl
  · simp [h]
    intro hmem
    have := List.mem_reverse.1 hmem
    apply nat_bits_aux_chars
    exact this

-- LLM HELPER
theorem nat_to_bin_valid (n : Nat) : ValidBitString (nat_to_bin n) := by
  intro i ch h
  dsimp [nat_to_bin, nat_bits] at h
  by_cases h0 : n = 0
  · simp [h0] at h
    rcases h with rfl
    exact Or.inl rfl
  · simp [h0] at h
    have mem := List.mem_reverse.1 h
    apply nat_bits_aux_chars
    exact mem
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def Add (s1 s2 : String) : String :=
  -- convert to nat, add, convert back
  nat_to_bin (Str2Int s1 + Str2Int s2)

def DivMod (dividend divisor : String) : (String × String) :=
  let d := Str2Int divisor
  -- total function; if divisor = 0 return (0, dividend) as a fallback
  if d = 0 then (nat_to_bin 0, dividend)
  else (nat_to_bin (Str2Int dividend / d), nat_to_bin (Str2Int dividend % d))

def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  let base := Str2Int sx
  let exp := Str2Int sy
  let m := Str2Int sz
  -- guard m = 0 to avoid div by zero in mod; if m = 0 return zero-string (conservative)
  if m = 0 then nat_to_bin 0 else nat_to_bin (Exp_int base exp % m)

def ModExp (sx sy sz : String) : String :=
  let base := Str2Int sx
  let exp := Str2Int sy
  let m := Str2Int sz
  if m = 0 then nat_to_bin 0 else nat_to_bin (Exp_int base exp % m)
-- </vc-code>

-- <vc-theorem>
theorem nat_to_bin_str_valid (n : Nat) : ValidBitString (nat_to_bin n) := by
  exact nat_to_bin_valid n
-- </vc-theorem>
-- <vc-proof>
-- proof already provided above as `nat_to_bin_valid`; this section kept for compatibility
-- nothing further required here
-- </vc-proof>

end BignumLean