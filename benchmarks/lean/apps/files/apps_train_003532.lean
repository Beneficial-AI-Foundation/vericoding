/-
Complete the function that accepts a valid string and returns an integer.

Wait, that would be too easy! Every character of the string should be converted to the hex value of its ascii code, then the result should be the sum of the numbers in the hex strings (ignore letters).

## Examples
```
"Yo" ==> "59 6f" ==> 5 + 9 + 6 = 20
"Hello, World!"  ==> 91
"Forty4Three"    ==> 113
```
-/

-- <vc-helpers>
-- </vc-helpers>

def hex_hash (s : String) : Nat :=
  sorry

theorem hex_hash_returns_nat (s : String) :
  hex_hash s ≥ 0 :=
sorry

theorem hex_hash_consistent (s : String) :
  hex_hash s = hex_hash s :=
sorry

theorem empty_string_hash :
  hex_hash "" = 0 :=
sorry

/-
info: 20
-/
-- #guard_msgs in
-- #eval hex_hash "Yo"

/-
info: 91
-/
-- #guard_msgs in
-- #eval hex_hash "Hello, World!"

/-
info: 113
-/
-- #guard_msgs in
-- #eval hex_hash "Forty4Three"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible