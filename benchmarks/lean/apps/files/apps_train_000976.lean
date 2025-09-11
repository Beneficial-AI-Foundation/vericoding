-- <vc-preamble>
def gcd (a b : Nat) : Nat :=
  sorry

def find_largest_gcd_1_subarray (arr : List Nat) : Int :=
  sorry

def reduce_gcd (l : List Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.firstElem (l : List Nat) (h : l.length > 0) : Nat :=
  match l with
  | [] => by contradiction
  | x::_ => x
-- </vc-definitions>

-- <vc-theorems>
theorem gcd_one_returns_full_length {arr : List Nat} (h1 : arr.length ≥ 2) (h2 : ∀ x ∈ arr, x ≥ 1) 
    (h3 : reduce_gcd arr = 1) :
  find_largest_gcd_1_subarray arr = arr.length := 
  sorry

theorem non_gcd_one_returns_negative {arr : List Nat} (h1 : arr.length ≥ 2) (h2 : ∀ x ∈ arr, x ≥ 1)
    (h3 : reduce_gcd arr > 1) :
  find_largest_gcd_1_subarray arr = -1 :=
  sorry

theorem return_bounds {arr : List Nat} (h1 : arr.length ≥ 2) (h2 : ∀ x ∈ arr, x ≥ 2) :
  find_largest_gcd_1_subarray arr = -1 ∨ 
  (1 ≤ find_largest_gcd_1_subarray arr ∧ find_largest_gcd_1_subarray arr ≤ arr.length) :=
  sorry

theorem same_elements_no_gcd_one {arr : List Nat} (h1 : arr.length ≥ 2) 
    (h2 : ∀ x ∈ arr, ∀ y ∈ arr, x = y) :
  ∀ x ∈ arr, x ≠ 1 → find_largest_gcd_1_subarray arr = -1 :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_largest_gcd_1_subarray [7, 2]

/-
info: -1
-/
-- #guard_msgs in
-- #eval find_largest_gcd_1_subarray [2, 2, 4]

/-
info: 4
-/
-- #guard_msgs in
-- #eval find_largest_gcd_1_subarray [6, 10, 15, 25]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded