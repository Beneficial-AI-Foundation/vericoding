-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def moves_to_make_zigzag (nums: List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem moves_nonnegative (nums: List Nat) :
  moves_to_make_zigzag nums ≥ 0 :=
sorry

theorem single_element_zero (nums: List Nat) :
  nums.length = 1 → moves_to_make_zigzag nums = 0 :=
sorry

theorem zigzag_no_moves (nums: List Nat) (h1: nums.length ≥ 2) 
  (h2: moves_to_make_zigzag nums = 0) 
  (i: Fin nums.length) (h3: 1 ≤ i.val) (h4: i.val < nums.length - 1) :
  let im1 : Fin nums.length := ⟨i.val - 1, sorry⟩
  let ip1 : Fin nums.length := ⟨i.val + 1, sorry⟩
  ((nums.get i > nums.get im1 ∧ nums.get i > nums.get ip1) ∨
   (nums.get i < nums.get im1 ∧ nums.get i < nums.get ip1)) :=
sorry

theorem symmetric_solution (nums: List Nat) :
  moves_to_make_zigzag nums = moves_to_make_zigzag nums.reverse :=
sorry
-- </vc-theorems>