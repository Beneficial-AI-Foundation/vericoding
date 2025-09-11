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
def nat_bits_rev : Nat -> List Char
| 0 => []
| m+1 =>
  let r := (m+1) % 2
  let q := (m+1) / 2
  (if r = 1 then '1' else '0') :: nat_bits_rev q

-- LLM HELPER
def bits_to_string (l : List Char) : String :=
  l.foldl (fun s c => s.push c) ""

-- LLM HELPER
def natToBinString (n : Nat) : String :=
  if n = 0 then "0" else bits_to_string (List.reverse (nat_bits_rev n))

-- LLM HELPER
theorem push_data (s : String) (c : Char) : (s.push c).data = s.data ++ [c] := by
  cases s
  simp [String.push]
  rfl

-- LLM HELPER
theorem foldl_push_data (s : String) (l : List Char) :
  (l.foldl (fun s c => s.push c) s).data = s.data ++ l := by
  induction l generalizing s
  case nil =>
    simp [List.foldl]
    rfl
  case cons x xs ih =>
    simp [List.foldl]
    have h := ih (s.push x)
    simp [push_data] at h
    simp [h]
    rfl

-- LLM HELPER
theorem bits_to_string_data_eq (l : List Char) :
  (bits_to_string l).data = l := by
  simp [bits_to_string]
  apply foldl_push_data

-- LLM HELPER
theorem Str2Int_bits_to_string_eq (l : List Char) :
  Str2Int (bits_to_string l) = l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
  simp [Str2Int, bits_to_string]
  have h := bits_to_string_data_eq l
  simp [h]

-- LLM HELPER
theorem Str2Int_bits_app_single (a : List Char) (c : Char) (acc : Nat) :
  (a ++ [c]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) acc =
    2 * (a.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) acc) + (if c = '1' then 1 else 0) := by
  induction a generalizing acc
  case nil =>
    simp [List.foldl]
    rfl
  case cons x xs ih =>
    simp [List.foldl]
    have h := ih ( (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) acc x )
    -- simplify using definition: (x :: xs).foldl f acc = xs.foldl f (f acc x)
    -- apply IH with accumulator f acc x
    simp [h]
    rfl
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- Implementations using conversion to/from Nat via Str2Int and natToBinString

def Add (s1 s2 : String) : String :=
  natToBinString (Str2Int s1 + Str2Int s2)

def Mul (s1 s2 : String) : String :=
  natToBinString (Str2Int s1 * Str2Int s2)

def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  let base := Str2Int sx
  let exponent := Str2Int sy
  let modulus := Str2Int sz
  natToBinString (Exp_int base exponent % modulus)

def ModExp (sx sy sz : String) : String :=
  natToBinString (Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz)
-- </vc-code>

-- <vc-theorem>
theorem build_ok : True
-- </vc-theorem>
-- <vc-proof>
:= by
  trivial
-- </vc-proof>

end BignumLean