-- <vc-preamble>
def maximum_sum_with_deletion (arr : List Int) : Int :=
  sorry

def list_maximum (arr : List Int) : Int :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_sum (arr : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible