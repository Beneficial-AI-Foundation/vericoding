def maximum_sum_with_deletion (arr : List Int) : Int :=
  sorry

def list_maximum (arr : List Int) : Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def list_sum (arr : List Int) : Int :=
  sorry

theorem positive_scaling {arr : List Int} {scale : Int}
  (h : arr ≠ []) (hs : scale > 0) :
  maximum_sum_with_deletion (List.map (· * scale) arr) = 
  maximum_sum_with_deletion arr * scale :=
sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval maximum_sum_with_deletion [1, -2, 0, 3]

/-
info: 3
-/
-- #guard_msgs in
-- #eval maximum_sum_with_deletion [1, -2, -2, 3]

/-
info: -1
-/
-- #guard_msgs in
-- #eval maximum_sum_with_deletion [-1, -1, -1, -1]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible