-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isValidHexColor (color : String) : Bool :=
sorry

def shadesOfGrey (n : Int) : List String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem shadesOfGrey_outputs_valid_list (n : Int) :
  ∀ x ∈ shadesOfGrey n, isValidHexColor x :=
sorry

theorem nonpositive_input_returns_empty {n : Int} (h : n ≤ 0) :
  shadesOfGrey n = [] :=
sorry

theorem output_length_constraints (n : Int) :
  List.length (shadesOfGrey n) = min (max 0 n) 254 :=
sorry

theorem values_monotonic_increasing {n : Int} (h1 : 1 ≤ n) (h2 : n ≤ 254) :
  let result := shadesOfGrey n
  let values := result.map (fun color => (color.take 3).toNat!)
  ∀ i j, i < j → j < values.length → values[i]! < values[j]! :=
sorry

theorem rgb_components_equal {n : Int} (h1 : 1 ≤ n) (h2 : n ≤ 254) :
  let result := shadesOfGrey n
  ∀ color ∈ result,
    color.get! ⟨1⟩ = color.get! ⟨3⟩ ∧
    color.get! ⟨3⟩ = color.get! ⟨5⟩ :=
sorry
-- </vc-theorems>