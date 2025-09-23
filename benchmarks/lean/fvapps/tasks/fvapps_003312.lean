-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def array_manip (arr : List Int) : List Int := sorry

theorem array_manip_length (arr : List Int) : 
  (array_manip arr).length = arr.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem array_manip_basic_properties (arr : List Int) (h : arr ≠ []) :
  let result := array_manip arr
  -- Result same length as input
  (result.length = arr.length) ∧
  -- Last element is -1
  (result.get? (result.length - 1) = some (-1)) ∧
  -- Each element is -1 or greater than input
  (∀ i : Fin arr.length, 
    have h1 : i.val < result.length := by rw [array_manip_length]; exact i.isLt
    (result.get ⟨i.val, h1⟩ = -1 ∨ result.get ⟨i.val, h1⟩ > arr.get i)) := sorry

theorem array_manip_elements_from_remaining (arr : List Int) (h : arr ≠ []) :
  let result := array_manip arr
  ∀ i : Fin (arr.length - 1),
    have h1 : i.val < result.length := by rw [array_manip_length]; sorry
    (result.get ⟨i.val, h1⟩ = -1 ∨ result.get ⟨i.val, h1⟩ ∈ arr.drop (i.val + 1)) := sorry

theorem array_manip_increasing_sequence (a b c : Int) (h1 : a < b) (h2 : b < c) :
  let arr := [a, b, c]
  array_manip arr = [b, c, -1] := sorry

theorem array_manip_no_greater_elements (arr : List Int) (h : arr ≠ []) :
  let result := array_manip arr
  ∀ i : Fin arr.length,
    have h1 : i.val < result.length := by rw [array_manip_length]; exact i.isLt
    (∀ j, i.val < j ∧ j < arr.length → arr.get ⟨j, by sorry⟩ ≤ arr.get i) →
    result.get ⟨i.val, h1⟩ = -1 := sorry
-- </vc-theorems>