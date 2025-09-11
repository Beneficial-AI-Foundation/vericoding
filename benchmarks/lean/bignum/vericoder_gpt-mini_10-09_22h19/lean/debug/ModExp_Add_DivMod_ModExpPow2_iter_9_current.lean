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
| n+1 =>
  let q := (n+1) / 2
  let r := (n+1) % 2
  (if r = 1 then '1' else '0') :: nat_bits_aux q

-- LLM HELPER
def nat_bits (n : Nat) : List Char :=
  if n = 0 then ['0'] else List.reverse (nat_bits_aux n)

-- LLM HELPER
def nat_to_bin (n : Nat) : String := String.mk (nat_bits n)

-- LLM HELPER
def bits_to_nat (bs : List Char) : Nat :=
  bs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- LLM HELPER: foldl append single-element lemma
theorem foldl_append_single (acc : Nat) (l : List Char) (b : Char) :
  (l ++ [b]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) acc
    = 2 * (l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) acc)
      + (if b = '1' then 1 else 0) := by
  induction l with
  | nil =>
    simp [List.foldl]
  | cons hd tl ih =>
    simp [List.foldl]
    -- foldl f acc (hd :: tl ++ [b]) = foldl f (f acc hd) (tl ++ [b])
    have : (tl ++ [b]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0))
            ((if hd = '1' then 1 else 0)) =
           2 * (tl.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) ((if hd = '1' then 1 else 0)))
           + (if b = '1' then 1 else 0) := by
      apply ih
    simp [this]
    -- Now show RHS matches by reassociating
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
def nat_bits_aux : Nat -> List Char
| 0 => []
| n+1 =>
  let q := (n+1) / 2
  let r := (n+1) % 2
  (if r = 1 then '1' else '0') :: nat_bits_aux q

-- LLM HELPER
def nat_bits (n : Nat) : List Char :=
  if n = 0 then ['0'] else List.reverse (nat_bits_aux n)

-- LLM HELPER
def nat_to_bin (n : Nat) : String := String.mk (nat_bits n)

-- LLM HELPER
def bits_to_nat (bs : List Char) : Nat :=
  bs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- LLM HELPER: foldl append single-element lemma
theorem foldl_append_single (acc : Nat) (l : List Char) (b : Char) :
  (l ++ [b]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) acc
    = 2 * (l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) acc)
      + (if b = '1' then 1 else 0) := by
  induction l with
  | nil =>
    simp [List.foldl]
  | cons hd tl ih =>
    simp [List.foldl]
    -- foldl f acc (hd :: tl ++ [b]) = foldl f (f acc hd) (tl ++ [b])
    have : (tl ++ [b]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0))
            ((if hd = '1' then 1 else 0)) =
           2 * (tl.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) ((if hd = '1' then 1 else 0)))
           + (if b = '1' then 1 else 0) := by
      apply ih
    simp [this]
    -- Now show RHS matches by reassociating
-- </vc-code>

end BignumLean