-- <vc-preamble>
def find_max_fun_factor (n d m : Nat) (arr : List Nat) : Nat := sorry

def sum_list : List Nat → Nat 
  | [] => 0
  | x::xs => x + sum_list xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_sum_of_largest (arr : List Nat) (n : Nat) : Nat :=
  sum_list ((List.toArray arr |>.qsort (· ≥ ·) |>.toList).take n)
-- </vc-definitions>

-- <vc-theorems>
theorem empty_above_m (n d : Nat) (arr : List Nat)
  (h1 : 0 < n ∧ n ≤ 100)
  (h2 : 0 < d ∧ d ≤ 10)
  (h3 : arr.length = n)
  (h4 : ∀ x ∈ arr, x < 1000) :
  find_max_fun_factor n d 1000 arr = list_sum_of_largest arr n := sorry

theorem single_element (n d m : Nat) (arr : List Nat)
  (h1 : 0 < n ∧ n ≤ 100)
  (h2 : 0 < d ∧ d ≤ 10)
  (h3 : 0 ≤ m ∧ m ≤ 100)
  (h4 : arr.length = n)
  (h5 : ∀ x ∈ arr, x = 0) :
  find_max_fun_factor n d m arr = 0 := sorry

/-
info: 48
-/
-- #guard_msgs in
-- #eval find_max_fun_factor 5 2 11 #[8, 10, 15, 23, 5]

/-
info: 195
-/
-- #guard_msgs in
-- #eval find_max_fun_factor 20 2 16 #[20, 5, 8, 2, 18, 16, 2, 16, 16, 1, 5, 16, 2, 13, 6, 16, 4, 17, 21, 7]

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_max_fun_factor 1 1 0 #[0]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: guarded