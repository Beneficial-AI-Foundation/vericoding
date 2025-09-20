-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def luxhouse (houses : List Nat) : List Nat := sorry

theorem luxhouse_preserves_length {houses : List Nat} (h : houses ≠ []) : 
  (luxhouse houses).length = houses.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem luxhouse_last_zero {houses : List Nat} (h : houses ≠ []) :
  houses.length > 0 → (luxhouse houses).getLast! = 0 := sorry

theorem luxhouse_non_negative {houses : List Nat} (h : houses.length ≥ 2) :
  ∀ x ∈ luxhouse houses, x ≥ 0 := sorry 

theorem luxhouse_identical_heights {h n : Nat} (len : n > 0) :
  let houses := List.replicate n h
  ∀ i, i < n - 1 → (luxhouse houses).get ⟨i, sorry⟩ = 1 ∧ 
      (luxhouse houses).getLast! = 0 := sorry
-- </vc-theorems>