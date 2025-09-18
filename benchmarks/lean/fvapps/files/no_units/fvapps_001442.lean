-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_boxes_remaining (boxes : List Nat) (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_boxes_result_bounds (boxes : List Nat) (n : Nat) (h : boxes.length = n) :
  min_boxes_remaining boxes n ≥ boxes.length / 2 ∧ 
  min_boxes_remaining boxes n ≤ boxes.length := by
  sorry

theorem min_boxes_is_nat (boxes : List Nat) (n : Nat) (h : boxes.length = n) :
  ∃ k : Nat, min_boxes_remaining boxes n = k := by
  sorry

theorem min_boxes_perm (boxes₁ boxes₂ : List Nat) (n : Nat) 
  (h₁ : boxes₁.length = n) (h₂ : boxes₂.length = n)
  (h₃ : ∀ x, boxes₁.count x = boxes₂.count x) :
  min_boxes_remaining boxes₁ n = min_boxes_remaining boxes₂ n := by
  sorry

theorem min_boxes_powers_two (size : Nat) :
  let boxes := List.map (fun i => 2^i) (List.range size)
  min_boxes_remaining boxes size = size/2 + size%2 := by
  sorry
-- </vc-theorems>