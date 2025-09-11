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
  (Nat_to_BitString q) ++ (if n % 2 = 1 then "1" else "0")
termination_by k => k

-- Str2Int for a string with one extra character appended equals 2 * Str2Int s + bit_val
theorem Str2Int_append_char (s : String) (c : Char) :
  Str2Int (s ++ String.singleton c) = 2 * Str2Int s + (if c = '1' then 1 else 0) := by
  simp [Str2Int, String.append, String.toList]
  -- foldl over (toList s ++ [c]) equals applying the step once to the fold over s
  have : List.foldl (fun (acc : Nat) (ch : Char) => 2 * acc + (if ch = '1' then 1 else 0)) 0 (String.toList s ++ [c]) =
             (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (List.foldl (fun (acc : Nat) (ch : Char) => 2 * acc + (if ch = '1' then 1 else 0)) 0 (String.toList s)) c := by
    apply List.foldl_append
  rw [this]; simp

theorem Nat_to_BitString_spec (k : Nat) :
  ValidBitString (Nat_to_BitString k) ∧ Str2Int (Nat_to_BitString k) = k := by
  induction k using Nat.strong_induction_on with
  | ih k =>
    cases k
    · -- k = 0
      simp [Nat_to_BitString, ValidBitString, Str2Int]
      constructor
      · intro i c h; simp at h; contradiction
      · rfl
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
          apply Nat.div_lt_self (by linarith)
          linarith
        have ihq := ih q qlt
        set s := Nat_to_BitString q with hs
        have Hvalid := ihq.left
        have Hval := ihq.right
        let bstr := (if n % 2 = 1 then "1" else "0")
        let bchar := (if n % 2 = 1 then '1' else '0')
        constructor
        · -- ValidBitString: characters come from s or from appended single char bchar
          intro i c h
          have : (s ++ bstr).get? i = some c := h
          -- there are three possibilities: i < s.length, i = s.length (the appended char), i > s.length (none)
          by_cases hlt : i < s.length
          · -- index inside s
            have : s.get? i = some c := by
              -- get? on append returns s.get? i when i < s.length
              simp [String.get?, String.append] at this
              -- after simplification it is exactly s.get? i = some c
              exact this
            apply Hvalid this
          · have heq : i = s.length ∨ i > s.length := by
              contrapose! hlt; exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _)
            cases heq
            · -- i = s.length, character is the appended one
              subst heq
              simp [String.get?, String.append] at this
              simp at this
              -- the appended string is single char bstr, so some c must be either '0' or '1'
              cases (n % 2 = 1) <;> simp [bstr, bchar] at this
              · -- bchar = '1'
                injection this with hc; clear this
                subst hc
                simp
              · injection this with hc; clear this
                subst hc
                simp
            · -- i > s.length: get? yields none, contradiction with some c
              simp [String.get?, String.append] at this
              contradiction
        · -- numeric equality: Str2Int (s ++ bstr) = 2 * Str2Int s + bit_val = n
          have : Str2Int (s ++ bstr) = 2 * Str2Int s + (if bchar = '1' then 1 else 0) := by
            -- apply the append-char lemma with the single character bchar
            have hb : s ++ bstr = s ++ String.singleton bchar := by
              -- bstr is "1" or "0", equal to String.singleton bchar
              cases (n % 2 = 1) <;> simp [bstr, bchar]
            rw [hb]
            exact Str2Int_append_char s bchar
          calc
            Str2Int (Nat_to_BitString n) = Str2Int (s ++ bstr) := by simp [Nat_to_BitString]; rfl
            _ = 2 * Str2Int s + (if bchar = '1' then 1 else 0) := by exact this
            _ = 2 * q + (n % 2) := by
              -- replace Str2Int s by q using induction hypothesis
              rw [Hval]; simp [bchar]
            _ = n := by
              -- standard division/mod decomposition: n = 2*q + (n % 2)
              exact (Nat.div_mod_eq n 2).symm
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
-- Proof included in the theorem above.
-- </vc-proof>

end BignumLean