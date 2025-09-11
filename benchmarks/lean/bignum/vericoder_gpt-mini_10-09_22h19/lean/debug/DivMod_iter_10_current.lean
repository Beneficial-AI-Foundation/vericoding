namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
open Std

/-- Produce the binary digits (LSB first) of n using unfoldr, then reverse. -/
def nat_to_bin_list (n : Nat) : List Char :=
  if n == 0 then ['0']
  else
    (List.unfoldr (fun m =>
      if m == 0 then none
      else
        let d := m % 2
        some (if d == 1 then '1' else '0', m / 2)
    ) n).reverse

def nat_to_bin_str (n : Nat) : String :=
  String.mk (nat_to_bin_list n)
-- </vc-helpers>

-- <vc-spec>
def DivMod (s1 s2 : String) : (String × String) :=
-- </vc-spec>
-- <vc-code>
let n1 := Str2Int s1
  let n2 := Str2Int s2
  if n2 == 0 then
    ("0", s1)
  else
    (nat_to_bin_str (n1 / n2), nat_to_bin_str (n1 % n2))
-- </vc-code>

-- <vc-theorem>
-- (No additional theorem content required for compilation in this task.)
-- </vc-theorem>
-- <vc-proof>
-- (No proof content required for compilation in this task.)
-- </vc-proof>

end BignumLean