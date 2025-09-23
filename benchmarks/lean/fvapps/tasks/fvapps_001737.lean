-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def productExceptSelf (nums : List Int) : List Int := sorry

theorem productExceptSelf_length (nums : List Int) (h : nums ≠ []) : 
  (productExceptSelf nums).length = nums.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem productExceptSelf_property {nums : List Int} {i : Fin nums.length}
  (h1 : nums.length ≥ 2) (h2 : ∀ x ∈ nums, -10 ≤ x ∧ x ≤ 10) :
  let result := productExceptSelf nums
  have h3 : result.length = nums.length := productExceptSelf_length nums (by 
    intro h
    have := h1
    rw [h] at this
    contradiction)
  result.get ⟨i, by rw [h3]; exact i.isLt⟩ = 
    (List.toArray nums).foldl (fun acc x => acc * x) 1 := sorry

theorem all_ones_case (nums : List Int) (h : ∀ x ∈ nums, x = 1) :
  ∀ x ∈ (productExceptSelf nums), x = 1 := sorry

theorem reciprocal_products {nums : List Int} {i j : Fin nums.length}
  (h1 : nums.length ≥ 2) (h2 : ∀ x ∈ nums, -10 ≤ x ∧ x ≤ 10)
  (hi : nums.get i ≠ 0) (hj : nums.get j ≠ 0) :
  let result := productExceptSelf nums
  have h3 : result.length = nums.length := productExceptSelf_length nums (by 
    intro h
    have := h1
    rw [h] at this
    contradiction)
  result.get ⟨i, by rw [h3]; exact i.isLt⟩ * nums.get i = 
  result.get ⟨j, by rw [h3]; exact j.isLt⟩ * nums.get j := sorry
-- </vc-theorems>