-- <vc-helpers>
-- </vc-helpers>

def pair_zeros (xs : List Int) : List Int := sorry

theorem pair_zeros_length_valid (xs : List Int) : 
  List.length (pair_zeros xs) ≤ List.length xs := sorry

theorem pair_zeros_preserves_nonzero (xs : List Int) (x : Int) :
  x ∈ pair_zeros xs → x ≠ 0 → x ∈ xs := sorry

theorem pair_zeros_zero_count (xs : List Int) :
  let input_zeros := (xs.filter (· = 0)).length
  let output_zeros := ((pair_zeros xs).filter (· = 0)).length
  output_zeros = (input_zeros + 1) / 2 := sorry

theorem pair_zeros_preserves_ordering (xs : List Int) :
  (xs.filter (· ≠ 0)) = ((pair_zeros xs).filter (· ≠ 0)) := sorry

/-
info: []
-/
-- #guard_msgs in
-- #eval pair_zeros []

/-
info: [1]
-/
-- #guard_msgs in
-- #eval pair_zeros [1]

/-
info: [0]
-/
-- #guard_msgs in
-- #eval pair_zeros [0]

/-
info: [0, 1, 2]
-/
-- #guard_msgs in
-- #eval pair_zeros [0, 1, 0, 2]

/-
info: [1, 0, 1, 2, 0]
-/
-- #guard_msgs in
-- #eval pair_zeros [1, 0, 1, 0, 2, 0, 0]

/-
info: [0, 0, 0]
-/
-- #guard_msgs in
-- #eval pair_zeros [0, 0, 0, 0, 0, 0]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible