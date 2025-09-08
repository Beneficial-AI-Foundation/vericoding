/-
Poor Cade has got his number conversions mixed up again!

Fix his ```convert_num()``` function so it correctly converts a base-10 ```int```eger, 
to the selected of ```bin```ary or ```hex```adecimal.

```#The output should be a string at all times```

```python
convert_num(number, base):
    if 'base' = hex:
        return int(number, 16)
    if 'base' = bin:
        return int(number, 2)
    return (Incorrect base input)
```
Please note, invalid ```number``` or ```base``` inputs will be tested.
In the event of an invalid ```number/base``` you should return:
```python
"Invalid number input"
or
"Invalid base input"
```
For each respectively.

Good luck coding! :D
-/

-- <vc-helpers>
-- </vc-helpers>

def Base := String 
def convert_num (n : Int) (b : Base) : String := sorry

theorem valid_conversion_hex (n : Int) :
  convert_num n "hex" = s!"0x{n}" := sorry

theorem valid_conversion_bin (n : Int) :
  convert_num n "bin" = s!"0b{n}" := sorry

theorem invalid_base (n : Int) (b : Base) :
  b ≠ "hex" → b ≠ "bin" → 
  convert_num n b = "Invalid base input" := sorry

theorem invalid_number_type (s : String) (b : Base) :
  convert_num 0 b = "Invalid number input" := sorry

/-
info: '0b1111010'
-/
-- #guard_msgs in
-- #eval convert_num 122 "bin"

/-
info: 'Invalid number input'
-/
-- #guard_msgs in
-- #eval convert_num "dog" "bin"

/-
info: '0x0'
-/
-- #guard_msgs in
-- #eval convert_num 0 "hex"

/-
info: 'Invalid base input'
-/
-- #guard_msgs in
-- #eval convert_num 123 "lol"

-- Apps difficulty: introductory
-- Assurance level: unguarded