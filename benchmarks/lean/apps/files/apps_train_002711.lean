def sum (l : List Int) : Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def peak (arr : List Int) : Int :=
  sorry

theorem peak_equal_sums (arr : List Int) (h_size : arr.length > 0) :
  let p := peak arr;
  p ≠ -1 →
  sum (arr.take (Int.toNat p)) = sum (arr.drop (Int.toNat (p + 1))) :=
  sorry

theorem peak_bounds (arr : List Int) :
  let p := peak arr;
  -1 ≤ p ∧ p < arr.length :=
  sorry

theorem peak_single_element (arr : List Int) (h : arr.length = 1) :
  peak arr = 0 :=
  sorry

theorem peak_empty :
  peak [] = -1 :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval peak [1, 2, 3, 5, 3, 2, 1]

/-
info: 2
-/
-- #guard_msgs in
-- #eval peak [1, 12, 3, 3, 6, 3, 1]

/-
info: -1
-/
-- #guard_msgs in
-- #eval peak [10, 20, 30, 40]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible