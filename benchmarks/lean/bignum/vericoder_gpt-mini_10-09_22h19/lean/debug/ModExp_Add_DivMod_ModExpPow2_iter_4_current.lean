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
    cases h with
    | head h0 =>
      let r := (m + 1) % 2
      by_cases hr : r = 1
      · simp [hr] at h0
        have : c = '1' := Eq.symm h0
        exact Or.inr this
      · simp [hr] at h0
        have : c = '0' := Eq.symm h0
        exact Or.inl this
    | tail ht =>
      exact ih ht

-- LLM HELPER
theorem nat_bits_chars (n : Nat) :
  ∀ c, c ∈ nat_bits n → c = '0' ∨ c = '1' := by
  intro c
  dsimp [nat_bits]
  by_cases h : n = 0
  · intro hmem
    simp [h] at hmem
    rcases hmem with rfl
    exact Or.inl rfl
  · intro hmem
    simp [h] at hmem
    have mem := (List.mem_reverse.1 hmem)
    exact nat_bits_aux_chars n mem

-- LLM HELPER
theorem nat_to_bin_valid (n : Nat) : ValidBitString (nat_to_bin n) := by
  intro i ch h
  -- Expand definitions to connect String.get? with underlying list membership.
  dsimp [nat_to_bin, nat_bits] at h
  -- We reason by cases on n.
  by_cases hn : n = 0
  · -- For n = 0, nat_to_bin 0 = "0"
    simp [hn] at h
    -- if "0".get? i = some ch then ch = '0'
    -- We use the fact that the only character in this string is '0'
    -- so the result must be '0'.
    -- Convert equality of get? into membership of the sole element.
    -- Expand String.get? to underlying list.get? by dsimp.
    dsimp at h
    -- now h states (['0'] : List Char).get? i = some ch
    -- get? returning some ch implies ch = '0' (the only list element)
    have : ch = '0' := by
      -- use List.get?_eq_some to show the returned element is the head
      -- We proceed by cases on i; the only possible some is at index 0.
      cases i with
      | ofNat idx =>
        -- the underlying get? for list will be none unless idx = 0, in which case ch = '0'
        -- we can inspect the computation by `dsimp` then `simp` to reduce it.
        dsimp [List.get?] at h
        -- now h is a computation on Nat index; use cases on idx
        cases idx with
        | zero =>
          simp at h
          injection h with hch
          exact hch
        | succ _ =>
          simp at h
          contradiction
    exact Or.inl this
  · -- For n ≠ 0, nat_to_bin n = String.mk (List.reverse (nat_bits_aux n))
    simp [hn] at h
    dsimp at h
    -- Now h says (List.reverse (nat_bits_aux n)).get? i = some ch.
    -- From get? = some ch we infer ch ∈ List.reverse (nat_bits_aux n),
    -- and by reversing membership we get ch ∈ nat_bits_aux n, then apply nat_bits_aux_chars.
    -- We perform a small lemma-proof inline for get? -> membership.
    have mem : ch ∈ List.reverse (nat_bits_aux n) := by
      -- Reduce to list.get? on the index; do case analysis on i to handle the Nat index.
      cases i with
      | ofNat idx =>
        dsimp [List.get?] at h
        -- We can use `List.get?_eq_some` style reasoning: when get? yields `some ch`, ch must be one of the list elements.
        -- We prove membership by induction on the list structure of nat_bits_aux n after reversing.
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
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
    cases h with
    | head h0 =>
      let r := (m + 1) % 2
      by_cases hr : r = 1
      · simp [hr] at h0
        have : c = '1' := Eq.symm h0
        exact Or.inr this
      · simp [hr] at h0
        have : c = '0' := Eq.symm h0
        exact Or.inl this
    | tail ht =>
      exact ih ht

-- LLM HELPER
theorem nat_bits_chars (n : Nat) :
  ∀ c, c ∈ nat_bits n → c = '0' ∨ c = '1' := by
  intro c
  dsimp [nat_bits]
  by_cases h : n = 0
  · intro hmem
    simp [h] at hmem
    rcases hmem with rfl
    exact Or.inl rfl
  · intro hmem
    simp [h] at hmem
    have mem := (List.mem_reverse.1 hmem)
    exact nat_bits_aux_chars n mem

-- LLM HELPER
theorem nat_to_bin_valid (n : Nat) : ValidBitString (nat_to_bin n) := by
  intro i ch h
  -- Expand definitions to connect String.get? with underlying list membership.
  dsimp [nat_to_bin, nat_bits] at h
  -- We reason by cases on n.
  by_cases hn : n = 0
  · -- For n = 0, nat_to_bin 0 = "0"
    simp [hn] at h
    -- if "0".get? i = some ch then ch = '0'
    -- We use the fact that the only character in this string is '0'
    -- so the result must be '0'.
    -- Convert equality of get? into membership of the sole element.
    -- Expand String.get? to underlying list.get? by dsimp.
    dsimp at h
    -- now h states (['0'] : List Char).get? i = some ch
    -- get? returning some ch implies ch = '0' (the only list element)
    have : ch = '0' := by
      -- use List.get?_eq_some to show the returned element is the head
      -- We proceed by cases on i; the only possible some is at index 0.
      cases i with
      | ofNat idx =>
        -- the underlying get? for list will be none unless idx = 0, in which case ch = '0'
        -- we can inspect the computation by `dsimp` then `simp` to reduce it.
        dsimp [List.get?] at h
        -- now h is a computation on Nat index; use cases on idx
        cases idx with
        | zero =>
          simp at h
          injection h with hch
          exact hch
        | succ _ =>
          simp at h
          contradiction
    exact Or.inl this
  · -- For n ≠ 0, nat_to_bin n = String.mk (List.reverse (nat_bits_aux n))
    simp [hn] at h
    dsimp at h
    -- Now h says (List.reverse (nat_bits_aux n)).get? i = some ch.
    -- From get? = some ch we infer ch ∈ List.reverse (nat_bits_aux n),
    -- and by reversing membership we get ch ∈ nat_bits_aux n, then apply nat_bits_aux_chars.
    -- We perform a small lemma-proof inline for get? -> membership.
    have mem : ch ∈ List.reverse (nat_bits_aux n) := by
      -- Reduce to list.get? on the index; do case analysis on i to handle the Nat index.
      cases i with
      | ofNat idx =>
        dsimp [List.get?] at h
        -- We can use `List.get?_eq_some` style reasoning: when get? yields `some ch`, ch must be one of the list elements.
        -- We prove membership by induction on the list structure of nat_bits_aux n after reversing.
-- </vc-code>

end BignumLean