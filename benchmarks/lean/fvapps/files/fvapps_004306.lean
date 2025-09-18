-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isValidHexColor (color : String) : Bool := sorry

def shadesOfGrey (n : Int) : List String := sorry

/- Each output is a valid list of strings where each string is a valid hex color -/
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded