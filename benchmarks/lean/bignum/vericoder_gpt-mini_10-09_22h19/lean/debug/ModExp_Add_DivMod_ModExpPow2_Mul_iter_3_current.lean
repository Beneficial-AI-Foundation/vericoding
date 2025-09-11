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

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

-- <vc-helpers>
-- LLM HELPER
-- Convert a nat to its binary representation as a string of '0'/'1'.
def NatToBin : Nat → String :=
  Nat.strongRecOn fun m rec =>
    if m = 0 then
      "0"
    else
      let q := m / 2
      let rest := rec q (by
        -- q < m for m > 0
        apply Nat.div_lt_self
        cases m
        · contradiction
        · simp)
      let bit := if m % 2 = 1 then '1' else '0'
      -- append bit to the end of rest
      String.mk (rest.data ++ [bit])

-- Prove that NatToBin produces a valid bitstring (only '0' or '1').
theorem ValidBitString_NatToBin (n : Nat) : ValidBitString (NatToBin n) := by
  apply Nat.strongInductionOn n
  intro m IH
  dsimp [NatToBin]
  by_cases hm : m = 0
  · simp [hm]
    intro i c h
    simp at h
    cases h
    injection h with hc
    subst hc
    right; rfl
  · -- m > 0
    let q := m / 2
    have qlt : q < m := by
      apply Nat.div_lt_self
      cases m
      · contradiction
      · simp
    have IHq := IH q qlt
    dsimp [NatToBin]
    -- rest is NatToBin q, which by IH is a valid bitstring
    intro i c h
    simp at h
    -- there are three cases for i: indexing into rest, indexing last bit, or out of bounds
    have : ∃ l, NatToBin q = String.mk l := by
      exists (NatToBin q).data; rfl
    -- analyze position
    cases i
    · -- i = 0, could be first char of rest or if rest has length 0, it's handled by rest
      -- we reason by using properties of get? on String.mk (list)
      simp at h
      -- get? 0 = some c implies c is '0' or '1' because rest is valid or it's the last bit
      -- we simply fallback to checking the char directly by computing the underlying list
      -- use brute force: the chars of the string are constructed from rest.data ++ [bit]
      have : (NatToBin q).data ++ [if m % 2 = 1 then '1' else '0'] = (NatToBin q).data ++ [if m % 2 = 1 then '1' else '0'] := rfl
      -- Simplify using IHq on any index that falls inside rest
      -- For the small mechanization here, use the fact that every character in rest is '0' or '1'
      -- and the appended bit is '0' or '1'
      cases (List.get? ((NatToBin q).data ++ [if m % 2 = 1 then '1' else '0']) 0) eqn:E
      · contradiction
      · simp at E
        injection h with hc
        subst hc
        -- the character must be either '0' or '1'
        have char_case : c = '0' ∨ c = '1' := by
          -- if the index is within the rest then IHq gives the claim, otherwise it's the last bit
          cases (List.get? (NatToBin q).data 0) with
          | some ch =>
            -- index 0 falls in rest
            have := by
              -- use ValidBitString property on rest
              apply
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
-- Convert a nat to its binary representation as a string of '0'/'1'.
def NatToBin : Nat → String :=
  Nat.strongRecOn fun m rec =>
    if m = 0 then
      "0"
    else
      let q := m / 2
      let rest := rec q (by
        -- q < m for m > 0
        apply Nat.div_lt_self
        cases m
        · contradiction
        · simp)
      let bit := if m % 2 = 1 then '1' else '0'
      -- append bit to the end of rest
      String.mk (rest.data ++ [bit])

-- Prove that NatToBin produces a valid bitstring (only '0' or '1').
theorem ValidBitString_NatToBin (n : Nat) : ValidBitString (NatToBin n) := by
  apply Nat.strongInductionOn n
  intro m IH
  dsimp [NatToBin]
  by_cases hm : m = 0
  · simp [hm]
    intro i c h
    simp at h
    cases h
    injection h with hc
    subst hc
    right; rfl
  · -- m > 0
    let q := m / 2
    have qlt : q < m := by
      apply Nat.div_lt_self
      cases m
      · contradiction
      · simp
    have IHq := IH q qlt
    dsimp [NatToBin]
    -- rest is NatToBin q, which by IH is a valid bitstring
    intro i c h
    simp at h
    -- there are three cases for i: indexing into rest, indexing last bit, or out of bounds
    have : ∃ l, NatToBin q = String.mk l := by
      exists (NatToBin q).data; rfl
    -- analyze position
    cases i
    · -- i = 0, could be first char of rest or if rest has length 0, it's handled by rest
      -- we reason by using properties of get? on String.mk (list)
      simp at h
      -- get? 0 = some c implies c is '0' or '1' because rest is valid or it's the last bit
      -- we simply fallback to checking the char directly by computing the underlying list
      -- use brute force: the chars of the string are constructed from rest.data ++ [bit]
      have : (NatToBin q).data ++ [if m % 2 = 1 then '1' else '0'] = (NatToBin q).data ++ [if m % 2 = 1 then '1' else '0'] := rfl
      -- Simplify using IHq on any index that falls inside rest
      -- For the small mechanization here, use the fact that every character in rest is '0' or '1'
      -- and the appended bit is '0' or '1'
      cases (List.get? ((NatToBin q).data ++ [if m % 2 = 1 then '1' else '0']) 0) eqn:E
      · contradiction
      · simp at E
        injection h with hc
        subst hc
        -- the character must be either '0' or '1'
        have char_case : c = '0' ∨ c = '1' := by
          -- if the index is within the rest then IHq gives the claim, otherwise it's the last bit
          cases (List.get? (NatToBin q).data 0) with
          | some ch =>
            -- index 0 falls in rest
            have := by
              -- use ValidBitString property on rest
              apply
-- </vc-code>

end BignumLean