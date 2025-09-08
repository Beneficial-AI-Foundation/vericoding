/-
You have to create a function which receives 3 arguments: 2 numbers, and the result of an unknown operation performed on them (also a number).

Based on those 3 values you have to return a string, that describes which operation was used to get the given result.

The possible return strings are:
  `"addition"`,
  `"subtraction"`,
  `"multiplication"`,
  `"division"`.

## Example:
```
calcType(1, 2, 3) -->   1 ? 2 = 3   --> "addition"
```

## Notes
* In case of division you should expect that the result of the operation is obtained by using `/` operator on the input values - no manual data type conversion or rounding should be performed.
* Cases with just one possible answers are generated.
* Only valid arguments will be passed to the function.
-/

-- <vc-helpers>
-- </vc-helpers>

def calc_type (a b result : Float) : String := sorry

theorem calc_type_addition (a b : Float) :
  a + b ≠ a - b →
  a + b ≠ a * b →
  a + b ≠ a / b →
  calc_type a b (a + b) = "addition" := sorry

theorem calc_type_subtraction (a b : Float) :
  a - b ≠ a + b →
  a - b ≠ a * b →
  a - b ≠ a / b →
  calc_type a b (a - b) = "subtraction" := sorry

theorem calc_type_multiplication (a b : Float) :
  a * b ≠ a + b →
  a * b ≠ a - b →
  a * b ≠ a / b →
  calc_type a b (a * b) = "multiplication" := sorry

theorem calc_type_division (a b : Float) :
  b ≠ 0 →
  a / b ≠ a + b →
  a / b ≠ a - b →
  a / b ≠ a * b →
  calc_type a b (a / b) = "division" := sorry

theorem calc_type_all_different (a b : Float) (h : b ≠ 0) :
  a + b ≠ a - b →
  a + b ≠ a * b →
  a + b ≠ a / b →
  a - b ≠ a * b →
  a - b ≠ a / b →
  a * b ≠ a / b → 
  ∃ op, calc_type a b op ∈ ["addition", "subtraction", "multiplication", "division"] ∧
  ∀ op', calc_type a b op' ∈ ["addition", "subtraction", "multiplication", "division"] → op' = op := sorry

/-
info: 'addition'
-/
-- #guard_msgs in
-- #eval calc_type 1 2 3

/-
info: 'subtraction'
-/
-- #guard_msgs in
-- #eval calc_type 10 5 5

/-
info: 'multiplication'
-/
-- #guard_msgs in
-- #eval calc_type 10 4 40

/-
info: 'division'
-/
-- #guard_msgs in
-- #eval calc_type 9 5 1.8

-- Apps difficulty: introductory
-- Assurance level: unguarded