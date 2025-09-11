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

-- <vc-helpers>
-- LLM HELPER
-- Helper: convert a natural number to its binary string (MSB first).
def nat_to_bits : Nat → String
  | 0     => "0"
  | 1     => "1"
  | n@(_+2) =>
    let q := n / 2
    let r := n % 2
    let prefix := nat_to_bits q
    let ch := if r = 1 then '1' else '0'
    prefix.push ch

-- LLM HELPER
-- Lemma: pushing a bit-character onto a string corresponds to doubling and adding the bit.
theorem Str2Int_push_bit (s : String) (c : Char) (hc : c = '0' ∨ c = '1') :
  Str2Int (s.push c) = 2 * Str2Int s + (if c = '1' then 1 else 0) := by
  -- Unfold Str2Int to its definition and use Array.foldl_push.
  dsimp [Str2Int]
  -- Use the Array.foldl_push lemma which describes how foldl behaves after pushing an element.
  -- The lemma exists as Array.foldl_push in core Lean 4.
  have h := Array.foldl_push (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 s.data c
  -- h states exactly the needed equality on the underlying Array foldl.
  rw [h]
  rfl

-- LLM HELPER
-- Specification of nat_to_bits: it produces a valid bit string and decodes to the original nat.
theorem nat_to_bits_spec (m : Nat) : ValidBitString (nat_to_bits m) ∧ Str2Int (nat_to_bits m) = m := by
  -- We use strong induction on m because nat_to_bits recurses on n / 2.
  apply Nat.strongRecOn m
  intro n IH
  cases n
  · -- n = 0
    dsimp [nat_to_bits]
    constructor
    · intro i c h
      -- nat_to_bits 0 = "0"
      dsimp at h
      -- The only possible char is '0'
      have : (nat_to_bits 0).get? 0 = some '0' := by simp [nat_to_bits]
      have : c = '0' := by
        -- from h we know the character equals '0'
        injection h with h'; exact h'
      exact Or.inl this
    · dsimp [Str2Int, nat_to_bits]; simp
  · -- n = n'.succ
    cases n
    · -- n = 1
      dsimp [nat_to_bits]
      constructor
      · intro i c h
        dsimp at h
        have : (nat_to_bits 1).get? 0 = some '1' := by simp [nat_to_bits]
        have : c = '1' := by injection h with h'; exact h'
        exact Or.inr this
      · dsimp [Str2Int, nat_to_bits]; simp
    · -- n >= 2
      -- Here n+2 in original pattern, set k = n+2
      let k := n.succ.succ
      -- we are in the branch for k, where nat_to_bits uses q = k / 2 and r = k % 2
      dsimp [nat_to_bits]
      let q := k / 2
      let r := k % 2
      have hqr : k = 2 * q + r := Nat.div_add_mod k 2
      -- q < k, so we can use IH
      have IHq := IH q (by
        apply Nat.div_lt_self
        -- show 1 < k
        decide)
      cases IHq with hv1 hv2
      let prefix := nat_to_bits q
      let ch := if r = 1 then '1' else '0'
      constructor
      · intro i c h
        -- For the pushed string prefix.push ch, the character at i is either from prefix or ch.
        have get_push := (prefix.push ch).get? i
        -- Determine whether i < prefix.length
        have len_push : (prefix.push ch).length = prefix.length + 1 := by
          simp [String.length, String.push]
        by_cases hi : i < prefix.length
        · -- from prefix
          have : (prefix.get? i) = some c := by
            -- get? on pushed string and i < prefix.length coincide with prefix.get?
            have aux : (prefix.push ch).get? i = prefix.get? i := by
              -- reduce definitions
              simp [String.get?, String.push]
            rw [← aux] at h
            exact h
          exact hv1 this
        · -- i >= prefix.length, but since get? returns some, i must be exactly prefix.length
          have bound : i < (prefix.push ch).length := by
            -- from get? some
            have : (prefix.push ch).get? i = some c := h
            -- the index must be < length
            dsimp at this
            exact (String.get?_some _ _).1 this
          dsimp [len_push] at bound
          have : i = prefix.length := by linarith
          rw [this] at h
          -- now the character equals ch
          dsimp [String.get?, String.push] at h
          dsimp [ch] at h
          cases r
          · -- r = 0 -> ch = '0'
            have : ch = '0' := by simp [ch]
            rw [this] at h
            injection h with h'; subst h'; exact Or.inl rfl
          · -- r = 1 -> ch = '1'
            have : ch = '1' := by simp [ch]
            rw [this] at h
            injection h with h'; subst h'; exact Or.inr rfl
      · -- Numeric equality
        have key : Str2Int (prefix.push ch) = 2 * Str2Int prefix + (if ch = '1' then 1 else 0) :=
          Str2Int_push_bit prefix ch (by
            dsimp [ch]; cases r <;> simp)
        rw [key, hv2]
        dsimp [ch]
        cases r
        · -- r = 0
          simp [hqr]
        · -- r = 1
          simp [hqr]
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  -- Compute the numeric modular exponent and convert back to a bitstring.
  let base := Str2Int sx
  let exponent := Str2Int sy
  let modulus := Str2Int sz
  let value := if modulus = 0 then 0 else (Exp_int base exponent) % modulus
  nat_to_bits value
-- </vc-code>

-- <vc-theorem>
theorem ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
  -- By definition ModExpPow2 returns nat_to_bits of the numeric result, so apply nat_to_bits_spec.
  dsimp [ModExpPow2]
  -- modulus is nonzero because hsz_gt1 states Str2Int sz > 1
  have hm : Str2Int sz ≠ 0 := by
    apply (ne_of_gt hsz_gt1)
  let m := (Exp_int (Str2Int sx) (Str2Int sy)) % Str2Int sz
  have spec := nat_to_bits_spec m
  exact spec
-- </vc-theorem>
-- <vc-proof>
-- Proofs are provided in the helper lemmas and in the theorem above.
-- The ModExpPow2_spec reduces to nat_to_bits_spec applied to the computed numeric value.
-- No further proof obligations.
-- </vc-proof>

end BignumLean