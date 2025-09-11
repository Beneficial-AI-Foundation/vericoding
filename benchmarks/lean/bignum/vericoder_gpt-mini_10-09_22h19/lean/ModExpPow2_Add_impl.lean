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
  | k+2   =>
    let n := k+2
    let q := n / 2
    let r := n % 2
    let prefix := nat_to_bits q
    let ch := if r = 1 then '1' else '0'
    String.push prefix ch

-- LLM HELPER
-- Lemma: pushing a bit-character onto a string corresponds to doubling and adding the bit.
theorem Str2Int_push_bit (s : String) (c : Char) (hc : c = '0' ∨ c = '1') :
  Str2Int (String.push s c) = 2 * Str2Int s + (if c = '1' then 1 else 0) := by
  dsimp [Str2Int]
  -- show that pushing a char appends it to the underlying list representation
  have : (String.push s c).data = s.data ++ [c] := by
    -- simplification unfolds String.push to list append
    simp [String.push]
  rw [this]
  -- foldl over appended list splits as foldl over prefix then over singleton
  let f := fun (acc : Nat) (ch : Char) => 2 * acc + (if ch = '1' then 1 else 0)
  have := List.foldl_append f s.data [c] 0
  -- rewrite using the foldl append property and compute the singleton case
  rw [this]
  simp [Str2Int]
  -- after simplification we get the desired expression
  rfl

-- LLM HELPER
-- Specification of nat_to_bits: it produces a valid bit string and decodes to the original nat.
theorem nat_to_bits_spec (m : Nat) : ValidBitString (nat_to_bits m) ∧ Str2Int (nat_to_bits m) = m := by
  induction m using Nat.strongRecOn with
  | intro k IH =>
    dsimp [nat_to_bits]
    cases k
    · -- k = 0 => m = 0
      constructor
      · intro i c h
        -- only possible character at index 0 is '0'
        have : (nat_to_bits 0).get? 0 = some '0' := by simp [nat_to_bits]
        injection h with heq; subst heq
        exact Or.inl rfl
      · -- numeric decode
        dsimp [Str2Int]; simp
    cases k
    · -- k = 1 => m = 1
      constructor
      · intro i c h
        have : (nat_to_bits 1).get? 0 = some '1' := by simp [nat_to_bits]
        injection h with heq; subst heq
        exact Or.inr rfl
      · dsimp [Str2Int]; simp
    -- k >= 2, so m = n where n = k+2
    let n := k+2
    let q := n / 2
    let r := n % 2
    have q_lt : q < n := by
      -- for n >= 2 we have n / 2 < n
      have : 0 < 2 := by decide
      apply Nat.div_lt_self n this
    let IHq := IH q q_lt
    cases IHq with hv_valid hv_val
    let prefix := nat_to_bits q
    let ch := if r = 1 then '1' else '0'
    constructor
    · -- ValidBitString: prefix valid by IH and ch is '0' or '1'
      intro i c h
      by_cases hi : i < prefix.length
      · -- character comes from prefix
        have aux : (String.get? (String.push prefix ch) i) = prefix.get? i := by
          -- String.get? on appended string for indices less than prefix.length returns same as prefix.get?
          -- simp unfolds the definition
          simp [String.get?, String.push, hi]
        have : prefix.get? i = some c := by
          rw [← aux] at h; exact h
        exact hv_valid this
      · -- i >= prefix.length -> it must be the last char equal to ch
        -- get? returning some for index >= length implies index = length and element is the pushed char
        have : i = prefix.length := by
          -- examine get? on String.push
          simp [String.get?, String.push] at h
          -- after simp the only case producing some is index = prefix.length
          injection h with heq; exact heq.symm
        rw [this] at h
        simp [String.get?, String.push] at h
        dsimp [ch] at h
        cases r
        case zero =>
          have : ch = '0' := by simp [ch]
          rw [this] at h
          injection h with heq; subst heq; exact Or.inl rfl
        case succ r' =>
          -- r' must be 0 since r < 2
          have r'_zero : r' = 0 := by
            have r_lt := Nat.mod_lt n (by decide)
            simp at r_lt
            linarith
          have : ch = '1' := by simp [ch, r'_zero]
          rw [this] at h
          injection h with heq; subst heq; exact Or.inr rfl
    · -- Numeric equality: use Str2Int_push_bit and IH on prefix
      have key := Str2Int_push_bit prefix ch (by
        dsimp [ch];
        cases r
        case zero => exact Or.inl rfl
        case succ r' =>
          -- r' must be 0
          have r'_zero : r' = 0 := by
            have r_lt := Nat.mod_lt n (by decide)
            simp at r_lt
            linarith
          simp [ch, r'_zero]; exact Or.inr rfl)
      -- rewrite using the push lemma and IH numeric value
      dsimp [Str2Int] at *
      rw [key, hv_val]
      -- conclude using relation n = 2 * q + r (div_add_mod)
      have hdiv := Nat.div_add_mod n 2
      dsimp at hdiv
      cases r
      case zero => simp [hdiv]
      case succ r' =>
        have r'_zero : r' = 0 := by
          have r_lt := Nat.mod_lt n (by decide)
          simp at r_lt
          linarith
        simp [hdiv, r'_zero]
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
  dsimp [ModExpPow2]
  let base := Str2Int sx
  let exponent := Str2Int sy
  let modulus := Str2Int sz
  -- modulus is nonzero because hsz_gt1 states Str2Int sz > 1
  have hm : modulus ≠ 0 := by
    intro h; rw [h] at hsz_gt1; linarith
  -- simplify the conditional using the nonzero fact
  have val_eq : (if modulus = 0 then 0 else (Exp_int base exponent) % modulus) = (Exp_int base exponent) % modulus := by
    by_cases h0 : modulus = 0
    · contradiction
    · simp [h0]
  let m := (Exp_int base exponent) % modulus
  -- use nat_to_bits_spec on the numeric result m
  have nat_spec := nat_to_bits_spec m
  constructor
  · -- ValidBitString part
    dsimp [ModExpPow2]
    rw [val_eq]
    exact nat_spec.1
  · -- Numeric equality part
    dsimp [ModExpPow2]
    rw [val_eq]
    exact nat_spec.2
-- </vc-theorem>
-- <vc-proof>
-- Proofs are provided inline in the theorem blocks above.
-- </vc-proof>

end BignumLean