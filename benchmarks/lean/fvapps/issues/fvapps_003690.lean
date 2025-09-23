-- <vc-preamble>
def is_prime (n : Nat) : Bool :=
  sorry

def total (arr : List Int) : Int :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sqrt (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem total_empty_property (arr : List Int) :
  arr = [] → total arr = 0 :=
sorry

theorem total_properties (arr : List Int) :
  total arr = (List.enum arr).foldl (fun acc (i, x) => if is_prime i then acc + x else acc) 0 :=
sorry

theorem total_sign (arr : List Int) :
  total arr ≥ 0 ∨ ∃ x ∈ arr, x < 0 :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval total []

/-
info: 7
-/
-- #guard_msgs in
-- #eval total [1, 2, 3, 4]

/-
info: 21
-/
-- #guard_msgs in
-- #eval total [1, 2, 3, 4, 5, 6, 7, 8]
-- </vc-theorems>