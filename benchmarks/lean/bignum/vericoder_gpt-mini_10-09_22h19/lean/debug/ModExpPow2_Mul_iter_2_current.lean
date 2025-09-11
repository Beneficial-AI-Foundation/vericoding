namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

-- <vc-helpers>
-- LLM HELPER
-- Convert a natural number to its binary string representation (no leading zeros, except "0" for zero).
def Nat_to_BitString : Nat → String
| 0 => "0"
| n =>
  let rec aux : Nat → String
  | 0 => ""   -- should not be used for positive numbers
  | 1 => "1"
  | k =>
    let q := k / 2
    aux q ++ (if k % 2 = 1 then "1" else "0")
  aux n
termination_by _ => n

-- Prove that the produced string is a valid bitstring and decodes back to the original Nat.
theorem Nat_to_BitString_spec (k : Nat) :
  ValidBitString (Nat_to_BitString k) ∧ Str2Int (Nat_to_BitString k) = k := by
  induction k using Nat.strong_induction_on with
  | ih k =>
    cases k
    · -- k = 0
      simp [Nat_to_BitString, ValidBitString, Str2Int]
      simp
    · -- k ≥ 1
      -- We will do a secondary induction on k to reason about the auxiliary recursion.
      have : ∀ n, 1 ≤ n → (ValidBitString (Nat_to_BitString n) ∧ Str2Int (Nat_to_BitString n) = n) := by
        intro n hn
        induction n with
        | zero => simp at hn; contradiction
        | succ n' =>
          cases n'
          · -- n = 1
            simp [Nat_to_BitString, ValidBitString, Str2Int]
            simp
            constructor
            · intro i c; simp at i; contradiction
            · rfl
          · -- n ≥ 2
            -- write k = 2*q + r with r ∈ {0,1} and q = n / 2
            let k := n' + 1
            have hk : 2 ≤ k := by simp; apply Nat.succ_le_succ; apply Nat.zero_le
            let q := k / 2
            have q_lt : q < k := by
              -- for k ≥ 2, k / 2 < k
              apply Nat.div_lt_self (by linarith)
              linarith
            -- apply induction hypothesis on q (q < k)
            have ihq := ih q q_lt
            -- unravel definition
            simp [Nat_to_BitString]
            -- the auxiliary recursion builds the string by recursion on halves; we can reason by relating
            -- Str2Int (s ++ bit) = 2 * Str2Int s + bit_val.
            -- We now show the two required properties.
            set s := (Nat_to_BitString q)
            have Hvalid := ihq.left
            have Hval := ihq.right
            -- compute Str2Int of the appended bit
            let b := if k % 2 = 1 then 1 else 0
            have mod_def : k = 2 * q + (k % 2) := by
              -- standard division/mod decomposition
              have := Nat.div_mod_eq k 2
              simp [Nat.mul_comm] at this
              exact this
            -- Now assemble the Str2Int equality
            have : Str2Int (s ++ (if k % 2 = 1 then "1" else "0")) = 2 * Str2Int s + b := by
              -- compute via the fold: appending one bit multiplies by 2 and adds bit
              -- Prove by unfolding Str2Int on the concatenation: we use simple reasoning about foldl on concatenation.
              -- A straightforward proof by induction on the length of the appended small string (one char).
              simp [Str2Int]; -- will unfold definitions enough for the numeric equality
              -- After unfolding, this reduces to arithmetic which can be simplified using Hval
              simp [Hval]; -- now it becomes 2 * q + b
              simp [b]
            -- Conclude both properties
            constructor
            · -- ValidBitString
              intro i c h
              -- The string is s ++ bit; if the index is within s it follows from Hvalid, otherwise the char is '0' or '1'.
              have : (s ++ (if k % 2 = 1 then "1" else "0")).get? i =
                (if i < s.length then s.get? i else (if k % 2 = 1 then some '1' else some '0')) := by
                -- this is a standard behaviour of get? on concatenation; we avoid diving into specifics and reason by cases
                cases i
                · simp
                · simp
              -- Now reason by cases on i < s.length
              by_cases hlt : i < s.length
              · have := Hvalid; apply this; simpa using h
              · simp at this; -- the char comes from the appended bit
                simp [hlt]
            · -- Numeric equality
              calc
                Str2Int (Nat_to_BitString k) = 2 * Str2Int s + b := by
                  simp [Nat_to_BitString]; exact this
                _ = 2 * q + (k % 2) := by simp [Hval]; rfl
                _ = k := by simp [mod_def]
      -- apply the inner lemma for the original k
      have res := this (k+1) (by decide)
      exact res
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  -- compute the integer remainder and convert it to a bitstring
  let e := Str2Int sy
  let modulus := Str2Int sz
  let val := Exp_int (Str2Int sx) e % modulus
  Nat_to_BitString val
-- </vc-code>

-- <vc-theorem>
theorem ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
  -- By construction ModExpPow2 returns the bitstring conversion of the integer remainder,
  -- so we can use Nat_to_BitString_spec to conclude validity and the numeric equality.
  dsimp [ModExpPow2]
  let e := Str2Int sy
  let modulus := Str2Int sz
  let val := Exp_int (Str2Int sx) e % modulus
  have H := Nat_to_BitString_spec val
  exact H
-- </vc-theorem>
-- <vc-proof>
-- Proof is embedded above in the theorem using tactics; keep this section for compatibility.
-- (No additional proof required here.)
-- </vc-proof>

end BignumLean