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
def str_to_nat (s : String) : Nat :=
  s.data.foldl bit_fold 0

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
def nat_to_len_bits (n len : Nat) : String :=
  String.mk (nat_to_len_bits_list n len)

-- LLM HELPER
def mod_pow (a e m : Nat) : Nat :=
  if m = 0 then 0
  else
    if e = 0 then 1 % m
    else (a % m * mod_pow a (e - 1) m) % m

-- LLM HELPER
theorem nat_to_len_bits_list_length (n len : Nat) : (nat_to_len_bits_list n len).length = len := by
  induction len generalizing n with
  | zero => simp [nat_to_len_bits_list]
  | succ len ih =>
    -- expand definition and consider the two branches of the if
    simp [nat_to_len_bits_list]
    split_ifs
    · -- branch where n ≥ 2^len
      -- length ('1' :: xs) = 1 + xs.length, apply ih to xs
      simp [ih (n - Nat.pow 2 len)]
    · -- branch where n < 2^len
      simp [ih n]

-- LLM HELPER
theorem nat_to_len_bits_length (n len : Nat) : (nat_to_len_bits n len).data.length = len := by
  simp [nat_to_len_bits]
  apply nat_to_len_bits_list_length
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExp (sx sy sz : String) : String :=
  let a := str_to_nat sx
  let e := str_to_nat sy
  let m := str_to_nat sz
  nat_to_len_bits (mod_pow a e m) sz.data.length
-- </vc-code>

-- <vc-theorem>
theorem ModExp_len (sx sy sz : String) : (ModExp sx sy sz).data.length = sz.data.length
-- </vc-theorem>
-- <vc-proof>
by
  simp [ModExp]
  apply nat_to_len_bits_length
-- </vc-proof>

end BignumLean