/-
Why would we want to stop to only 50 shades of grey? Let's see to how many we can go. 

Write a function that takes a number n as a parameter and return an array containing n shades of grey in hexadecimal code (`#aaaaaa` for example). The array should be sorted in ascending order starting with `#010101`, `#020202`, etc. (using lower case letters).

```python
def shades_of_grey(n):
  return '''n shades of grey in an array'''
```

As a reminder, the grey color is composed by the same number of red, green and blue: `#010101`, `#aeaeae`, `#555555`, etc. Also, `#000000` and `#ffffff` are not accepted values.

When n is negative, just return an empty array.
If n is higher than 254, just return an array of 254 elements.

Have fun
-/

-- <vc-helpers>
-- </vc-helpers>

def isValidHexColor (color : String) : Bool := sorry

def shadesOfGrey (n : Int) : List String := sorry

/- Each output is a valid list of strings where each string is a valid hex color -/

theorem shadesOfGrey_outputs_valid_list (n : Int) : 
  ∀ x ∈ shadesOfGrey n, isValidHexColor x := sorry

/- Non-positive inputs return empty list -/

theorem nonpositive_input_returns_empty {n : Int} (h : n ≤ 0) :
  shadesOfGrey n = [] := sorry

/- Output length is constrained between 0 and min(n, 254) -/

theorem output_length_constraints (n : Int) :
  List.length (shadesOfGrey n) = min (max 0 n) 254 := sorry

/- Values are monotonically increasing -/

theorem values_monotonic_increasing {n : Int} (h1 : 1 ≤ n) (h2 : n ≤ 254) :
  let result := shadesOfGrey n
  let values := result.map (fun color => (color.take 3).toNat!)
  ∀ i j, i < j → j < values.length → values[i]! < values[j]! := sorry

/- RGB components are equal for each color -/

theorem rgb_components_equal {n : Int} (h1 : 1 ≤ n) (h2 : n ≤ 254) :
  let result := shadesOfGrey n
  ∀ color ∈ result, 
    color.get! ⟨1⟩ = color.get! ⟨3⟩ ∧ 
    color.get! ⟨3⟩ = color.get! ⟨5⟩ := sorry

/-
info: []
-/
-- #guard_msgs in
-- #eval shades_of_grey -1

/-
info: ['#010101']
-/
-- #guard_msgs in
-- #eval shades_of_grey 1

/-
info: ['#010101', '#020202', '#030303']
-/
-- #guard_msgs in
-- #eval shades_of_grey 3

-- Apps difficulty: introductory
-- Assurance level: unguarded