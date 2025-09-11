namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

-- <vc-helpers>
-- LLM HELPER
def bit_fold (acc : Nat) (ch : Char) : Nat :=
  2 * acc + (if ch = '1' then 1 else 0)

-- LLM HELPER
def nat_to_len_bits_list : Nat → Nat → List Char
  | _, 0 => []
  | n, len+1 =>
    let pow := Nat.pow 2 len
    if n ≥ pow then
      '1' :: nat_to_len_bits_list (n - pow) len
    else
      '0' :: nat_to_len_bits_list n len

-- LLM HELPER
def nat_to_len_bits (n len
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
def bit_fold (acc : Nat) (ch : Char) : Nat :=
  2 * acc + (if ch = '1' then 1 else 0)

-- LLM HELPER
def nat_to_len_bits_list : Nat → Nat → List Char
  | _, 0 => []
  | n, len+1 =>
    let pow := Nat.pow 2 len
    if n ≥ pow then
      '1' :: nat_to_len_bits_list (n - pow) len
    else
      '0' :: nat_to_len_bits_list n len

-- LLM HELPER
def nat_to_len_bits (n len
-- </vc-code>

end BignumLean