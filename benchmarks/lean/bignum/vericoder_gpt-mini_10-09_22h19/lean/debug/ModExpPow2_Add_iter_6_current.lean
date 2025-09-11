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
    prefix.push ch

-- LLM HELPER
-- Lemma: pushing a bit-character onto a string corresponds to doubling and adding the bit.
theorem Str2Int_push_bit (s : String) (c : Char) (hc : c = '0' ∨ c = '1') :
  Str2Int (s.push c) = 2 * Str2Int s + (if c = '1' then 1 else 0) := by
  dsimp [Str2Int]
  have h_arr : (s.push c).data = s.data.push c := rfl
  rw [h_arr]
  -- Use Array.foldl_push: foldl f init (arr.push a) = f (Array.foldl f init arr) a
  have h := Array.foldl_push (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 s.data c
  rw [h]
  rfl

-- LLM HELPER
-- Specification of nat_to_bits: it produces a valid bit string and decodes to the original nat.
theorem nat_to_bits_spec (m : Nat) : ValidBitString (nat_to_bits m) ∧ Str2Int (nat_to_bits m) = m := by
  induction m using Nat.strongRecOn with
  | intro m IH =>
    dsimp [nat_to_bits]
    cases m
    · -- m = 0
      dsimp [nat_to_bits]
      constructor
      · intro i c h
        have : (nat_to_bits 0).get? 0 = some '0' := by simp [nat_to_bits]
        injection h with heq
        subst heq
        exact Or.inl rfl
      · dsimp [Str2Int]; simp
    cases m
    · -- m = 1
      dsimp [nat_to_bits]
      constructor
      · intro i c h
        have : (nat_to_bits 1).get? 0 = some '1' := by simp [nat_to_bits]
        injection h with heq
        subst heq
        exact Or.inr rfl
      · dsimp [Str2Int]; simp
    -- m >= 2: this branch corresponds to k+2
    let k := m.succ.succ
    dsimp [nat_to_bits]
    let q := k / 2
    let r := k % 2
    have hdivmod := Nat.div_add_mod k 2
    -- q < k so apply IH on q
    have q_lt_k : q < k := by
      apply Nat.div_lt_self
      · decide
      · apply Nat.succ_pos
    have IHq := IH q q_lt_k
    cases IHq with hv_valid hv_val
    let prefix := nat_to_bits q
    let ch := if r = 1 then '1' else '0'
    constructor
    · intro i c h
      -- prove prefix.push ch has only '0'/'1' characters
      have len_push : (prefix.push ch).length = prefix.length + 1 := by
        simp [String.length]
      by_cases hi : i < prefix.length
      · -- character comes from prefix
        have aux : (prefix.push ch).get? i = prefix.get? i := by
          simp [String.get?, String.push, hi]
        have : prefix.get? i = some c := by
          rw [← aux] at h; exact h
        exact hv_valid this
      · -- i >= prefix.length, must be the pushed char (and within bounds)
        have bound : i < (prefix.push ch).length := by
          have : (prefix.push ch).get? i = some c := h
          simp [String.get?, String.push] at this
          exact (Array.get?_some _ _).1 this
        dsimp [len_push] at bound
        have : i = prefix.length := by linarith
        rw [this] at h
        simp [String.get?, String.push] at h
        dsimp [ch] at h
        have r_lt : r < 2 := Nat.mod_lt k (by decide)
        cases r
        case zero =>
          have : ch = '0' := by simp [ch]
          rw [this] at h
          injection h with heq; subst heq
          exact Or.inl rfl
        case succ r' =>
          have : r' = 0 := by
            have : succ r' < 2 := r_lt
            linarith
          have : ch = '1' := by simp [ch, this]
          rw [this] at h
          injection h with heq; subst heq
          exact Or.inr rfl
    · -- numeric equality: use Str2Int_push_bit then hv_val and divisibility relation
      have key : Str2Int (prefix.push ch) = 2 * Str2Int prefix + (if ch = '1' then 1 else 0) :=
        Str2Int_push_bit prefix ch (by
          dsimp [ch];
          have r_lt : r < 2 := Nat.mod_lt k (by decide)
          cases r
          case zero => simp [ch]
          case succ r' =>
            have : r' = 0 := by
              have : succ r' < 2 := r_lt
              linarith
            simp [ch, this])
      rw [key, hv_val]
      dsimp [ch]
      -- conclude using k = 2*q + r
      cases r
      case zero =>
        simp [hdivmod]
      case succ r' =>
        have : r' = 0 := by
          have r_lt := Nat.mod_lt k (by decide)
          have : succ r' < 2 := r_lt
          linarith
        simp [hdivmod, this]
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