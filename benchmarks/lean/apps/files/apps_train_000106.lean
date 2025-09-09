-- <vc-helpers>
-- </vc-helpers>

def is_array_sharpenable (n : Nat) (arr : List Int) : Bool :=
  sorry

theorem array_len_matches_param {n : Nat} {arr : List Int} 
  (h1 : arr.length > 0) :
  is_array_sharpenable n arr = is_array_sharpenable arr.length arr :=
sorry

theorem negative_values_work {n : Nat} {arr : List Int}
  (h1 : arr.length > 0) :
  ∃ result : Bool, is_array_sharpenable n arr = result :=
sorry

theorem strictly_decreasing_large_numbers {n : Nat} {arr : List Int}
  (h1 : arr.length > 0)
  (h2 : ∀ x ∈ arr, x > 0)
  (h3 : ∀ x ∈ arr, ∃ y : Int, y = x * n)
  (h4 : ∀ (i j : Fin arr.length), i < j → arr.get i > arr.get j) :
  is_array_sharpenable n arr = true :=
sorry

theorem all_zeros_not_sharpenable {n : Nat} {arr : List Int}
  (h1 : n > 1)
  (h2 : arr = List.replicate n 0) :
  is_array_sharpenable n arr = false :=
sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_array_sharpenable 1 [248618]

/-
info: True
-/
-- #guard_msgs in
-- #eval is_array_sharpenable 3 [12, 10, 8]

/-
info: False
-/
-- #guard_msgs in
-- #eval is_array_sharpenable 4 [0, 1, 1, 0]

-- Apps difficulty: interview
-- Assurance level: unguarded