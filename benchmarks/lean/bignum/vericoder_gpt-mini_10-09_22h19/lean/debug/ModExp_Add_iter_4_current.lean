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
def bits_of_nat : Nat → List Bool
  | 0     => []
  | n+1   =>
    let m := n + 1
    bits_of_nat (m / 2) ++ [m % 2 = 1]

-- LLM HELPER
def nat_to_bits_rec (n : Nat) : List Char :=
  (bits_of_nat n).map fun b => if b then '1' else '0'

-- LLM HELPER
def nat_to_bitlist (n : Nat) : List Char :=
  if n = 0 then ['0'] else nat_to_bits_rec n

-- LLM HELPER
def nat_to_bitstring (n : Nat) : String :=
  String.mk (nat_to_bitlist n)
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExp (sx sy sz : String) : String :=
  let base := Str2Int sx
  let exp := Str2Int sy
  let m := Str2Int sz
  if m = 0 then nat_to_bitstring 0 else
    nat_to_bitstring ((Exp_int base exp) % m)
-- </vc-code>

end BignumLean