-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_turbulence_size (arr : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem turbulence_size_bounds {arr : List Int} (h : arr.length ≥ 1) : 
  1 ≤ max_turbulence_size arr ∧ max_turbulence_size arr ≤ arr.length :=
  sorry

theorem same_elements_turbulence {arr : List Int} (h : arr.length ≥ 1) :
  let same := List.replicate arr.length (arr.get ⟨0, by exact Nat.zero_lt_of_lt h⟩)
  max_turbulence_size same = 1 :=
  sorry

theorem strictly_increasing_turbulence {arr : List Int} (h : arr.length ≥ 2) :
  max_turbulence_size arr = 2 :=
  sorry

theorem single_element_turbulence {arr : List Int} (h : arr.length ≥ 1) :
  max_turbulence_size [arr.get ⟨0, by exact Nat.zero_lt_of_lt h⟩] = 1 :=
  sorry

theorem pair_turbulence {arr : List Int} (h : arr.length ≥ 2) :
  let first := arr.get ⟨0, by exact Nat.zero_lt_of_lt h⟩
  let second := arr.get ⟨1, by exact h⟩
  max_turbulence_size [first, second] = if first = second then 1 else 2 :=
  sorry
-- </vc-theorems>