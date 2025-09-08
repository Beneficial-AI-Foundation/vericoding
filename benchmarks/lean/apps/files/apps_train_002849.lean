/-
The rgb function is incomplete. Complete it so that passing in RGB decimal values will result in a hexadecimal representation being returned. Valid decimal values for RGB are 0 - 255. Any values that fall out of that range must be rounded to the closest valid value.

Note: Your answer should always be 6 characters long, the shorthand with 3 will not work here.

The following are examples of  expected output values:
```python
rgb(255, 255, 255) # returns FFFFFF
rgb(255, 255, 300) # returns FFFFFF
rgb(0,0,0) # returns 000000
rgb(148, 0, 211) # returns 9400D3
```
```if:nasm

char \*rgb(int r, int g, int b, char \*outp)

```
-/

def isHexDigit (c : Char) : Bool := sorry

def rgb (r g b : Int) : String := sorry

-- <vc-helpers>
-- </vc-helpers>

def hexStringToNat (s : String) : Nat := sorry

theorem rgb_output_format (r g b : Int) :
  let result := rgb r g b
  (result.length = 6) ∧ 
  (result.data.all isHexDigit)
  := sorry

theorem rgb_valid_inputs (r g b : Int) 
  (hr : 0 ≤ r ∧ r ≤ 255)
  (hg : 0 ≤ g ∧ g ≤ 255)
  (hb : 0 ≤ b ∧ b ≤ 255) :
  let result := rgb r g b
  let r_hex := result.take 2
  let g_hex := result.drop 2 |>.take 2
  let b_hex := result.drop 4 |>.take 2
  (hexStringToNat r_hex = r) ∧
  (hexStringToNat g_hex = g) ∧
  (hexStringToNat b_hex = b)
  := sorry

theorem rgb_negative_inputs (r g b : Int)
  (hr : r < 0)
  (hg : g < 0)
  (hb : b < 0) :
  rgb r g b = "000000"
  := sorry

theorem rgb_large_inputs (r g b : Int)
  (hr : r > 255)
  (hg : g > 255)
  (hb : b > 255) :
  rgb r g b = "FFFFFF"
  := sorry

/-
info: '000000'
-/
-- #guard_msgs in
-- #eval rgb 0 0 0

/-
info: '010203'
-/
-- #guard_msgs in
-- #eval rgb 1 2 3

/-
info: '00FF7D'
-/
-- #guard_msgs in
-- #eval rgb -20 275 125

-- Apps difficulty: introductory
-- Assurance level: unguarded