-- <vc-preamble>
def find_max_diff (N : Nat) (K : Nat) (arr : List Int) : Int :=
sorry

def list_max (arr : List Int) : Int :=
sorry

def list_min (arr : List Int) : Int :=
sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_sort (arr : List Int) : List Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_max_diff_non_negative (N : Nat) (K : Nat) (arr : List Int) 
    (h : arr.length > 0) : 
  find_max_diff N K arr ≥ 0 :=
sorry

theorem find_max_diff_reverse_invariant (N : Nat) (K : Nat) (arr : List Int)
    (h : arr.length > 0) :
  find_max_diff N K arr = find_max_diff N K arr.reverse :=
sorry

theorem find_max_diff_single_element (N : Nat) (K : Nat) (arr : List Int)
    (h : arr.length = 1) :
  find_max_diff N K arr = 2 * K :=
sorry

/-
info: 10
-/
-- #guard_msgs in
-- #eval find_max_diff 4 3 [4, 2, 5, 1]

/-
info: 13
-/
-- #guard_msgs in
-- #eval find_max_diff 3 5 [2, 5, 3]

/-
info: 6
-/
-- #guard_msgs in
-- #eval find_max_diff 2 2 [1, 3]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible