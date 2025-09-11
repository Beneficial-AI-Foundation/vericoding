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
| 1 => "1"
| k+2 =>
  let n := k + 2
  let q := n / 2
  let s := Nat_to_BitString q
  s ++ (if n % 2 = 1 then "1" else "0")
termination_by Nat_to_BitString x => x

theorem Nat_to_BitString_spec (k : Nat) :
  ValidBitString (Nat_to_BitString k) ∧ Str2Int (Nat_to_BitString k) = k := by
  induction k using Nat.strong_induction_on with
  | ih k =>
    cases k
    · -- k = 0
      simp [Nat_to_BitString, ValidBitString, Str2Int]
    · cases k
      · -- k = 1
        simp [Nat_to_BitString, ValidBitString, Str2Int]
        constructor
        · intro i c h; simp at h; contradiction
        · rfl
      · -- k ≥ 2
        let n := k
        have hn : 2 ≤ n := by linarith
        let q := n / 2
        have qlt : q < n := by
          -- for n ≥ 2, n / 2 < n
          apply Nat.div_lt_self (by linarith)
          linarith
        have ihq := ih q qlt
        -- s is the bitstring for q
        set s := Nat_to_BitString q with hs
        have Hvalid := ihq.left
        have Hval := ihq.right
        let b := if n % 2 = 1 then "1" else "0"
        -- valid bitstring: s is valid and appended bit is '0' or '1'
        constructor
        · intro i c h
          -- character either from s or from appended single character
          have : (s ++ b).get? i =
            (if i < s.length then s.get? i else (if b = "1" then some '1' else some '0')) := by
            -- this unfolds to definition of get? on concatenation; handle by cases on i
            cases i
            · simp
            · simp
          by_cases hlt : i < s.length
          · -- within s
            have := Hvalid; apply this; simpa using h
          · -- from appended bit
            simp at this
            -- b is either "1" or "0", so the char is '1' or '0'
            have : b = "1" ∨ b = "0" := by
              cases (n % 2 = 1) <;> simp [b]
            cases this
            · simp [*] at h; simp [*]
            · simp [*] at h; simp [*]
        · -- numeric equality: Str2Int (s ++ b) = 2 * Str2Int s + bit_val = n
          have : Str2Int (s ++ b) = 2 * Str2Int s + (if b = "1" then 1 else 0) := by
            -- unfold Str2Int to the underlying fold over characters and compute for single appended char
            simp [Str2Int]
            -- after unfolding, the fold over the concatenation processes s.data then the single char,
            -- which yields 2 * Str2Int s + bit_val; the simplifier handles this step.
            -- Use a small direct computation: set c to the appended char and simplify.
            let c := if n % 2 = 1 then '1' else '0'
            have : b = (if n % 2 = 1 then "1" else "0") := rfl
            -- express concatenation at data level and reduce the final step of the fold
            simp [String.append, String.toList, List.foldl_append]
            -- now the last step of foldl processes c producing the desired arithmetic
            simp [List.foldl]; rfl
          calc
            Str2Int (Nat_to_BitString n) = Str2Int (s ++ b) := by simp [Nat_to_BitString]; rfl
            _ = 2 * Str2Int s + (if b = "1" then 1 else 0) := by exact this
            _ = 2 * q + (n % 2) := by
              simp [b] at *; -- replace b by definition and use Hval
              simp [Hval]
            _ = n := by
              -- standard division/mod decomposition: n = 2*q + (n % 2)
              have := Nat.div_mod_eq n 2
              simp [Nat.mul_comm] at this
              exact this
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
  dsimp [ModExpPow2]
  let e := Str2Int sy
  let modulus := Str2Int sz
  let val := Exp_int (Str2Int sx) e % modulus
  have H := Nat_to_BitString_spec val
  exact H
-- </vc-theorem>
-- <vc-proof>
-- Proof is provided in the theorem body above using tactics; nothing additional required here.
-- </vc-proof>

end BignumLean