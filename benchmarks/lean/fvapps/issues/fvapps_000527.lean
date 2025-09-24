-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_tower_height (triangles : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_max_tower_height_non_negative (triangles : List Nat) 
  (h : ∀ x ∈ triangles, x > 0) : 
  find_max_tower_height triangles ≥ 0 :=
sorry

theorem find_max_tower_height_upper_bound (triangles : List Nat)
  (h : ∀ x ∈ triangles, x > 0) :
  find_max_tower_height triangles ≤ triangles.length / 2 :=
sorry

theorem find_max_tower_height_singleton (triangles : List Nat)
  (h : triangles.length = 1) 
  (h2 : ∀ x ∈ triangles, x > 0) :
  find_max_tower_height triangles = 0 :=
sorry

theorem find_max_tower_height_composition 
  (triangle_lists : List (List Nat))
  (h : ∀ l ∈ triangle_lists, ∀ x ∈ l, x > 0)
  (h2 : triangle_lists ≠ []) :
  find_max_tower_height (List.join triangle_lists) ≥ 
  (triangle_lists.map find_max_tower_height).maximum?.get! :=
sorry

theorem find_max_tower_height_pairs (triangles : List Nat)
  (h : triangles.length ≥ 2)
  (h2 : ∀ x ∈ triangles, x > 0) :
  find_max_tower_height triangles ≥ 
  (List.zip (triangles.take (triangles.length - 1)) (triangles.tail!)
    |>.filter (fun p => p.1 = p.2)
    |>.length) / 2 :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_max_tower_height [5, 4, 2, 2, 3, 2, 1, 3, 2, 7, 4, 9, 9, 9]

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_max_tower_height [1, 2, 1]

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_max_tower_height [1, 1, 1]
-- </vc-theorems>