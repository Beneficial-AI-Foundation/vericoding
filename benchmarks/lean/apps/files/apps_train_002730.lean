-- <vc-helpers>
-- </vc-helpers>

def is_nice (arr : List Int) : Bool := 
  sorry

theorem nice_list_nonempty {arr : List Int} : 
  is_nice arr → arr ≠ [] :=
  sorry

theorem nice_list_has_neighbors {arr : List Int} {n : Int} :
  is_nice arr → n ∈ arr → 
  (n + 1 ∈ arr) ∨ (n - 1 ∈ arr) :=
  sorry

theorem empty_list_not_nice :
  ¬is_nice [] :=
  sorry

theorem singleton_not_nice (x : Int) :
  ¬is_nice [x] :=
  sorry

theorem sequential_is_nice_ascending :
  is_nice [0, 1, 2] :=
  sorry

theorem sequential_is_nice_negative :
  is_nice [-2, -1, 0] :=
  sorry

theorem sequential_is_nice_descending :
  is_nice [10, 9, 8] :=
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_nice [2, 10, 9, 3]

/-
info: False
-/
-- #guard_msgs in
-- #eval is_nice [3, 4, 5, 7]

/-
info: True
-/
-- #guard_msgs in
-- #eval is_nice [0, -1, 1]

-- Apps difficulty: introductory
-- Assurance level: unguarded