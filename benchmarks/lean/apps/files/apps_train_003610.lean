-- <vc-helpers>
-- </vc-helpers>

def List.update_inventory (cur_stock: List (Nat × String)) (new_stock: List (Nat × String)) : List (Nat × String) := 
  sorry

theorem update_inventory_sorted (cur_stock new_stock: List (Nat × String)) :
  let result := List.update_inventory cur_stock new_stock
  ∀ i j, i < j → j < result.length → (result.get ⟨i, by sorry⟩).2 ≤ (result.get ⟨j, by sorry⟩).2 := 
  sorry

theorem update_inventory_unique_length (cur_stock new_stock: List (Nat × String)) :
  let result := List.update_inventory cur_stock new_stock
  let unique_items := (cur_stock ++ new_stock).map Prod.snd |>.eraseDups
  result.length = unique_items.length :=
  sorry

theorem update_inventory_quantities (cur_stock new_stock: List (Nat × String)) (item : String) :
  let result := List.update_inventory cur_stock new_stock
  let expected_sum := (cur_stock ++ new_stock).filter (·.2 = item) |>.map Prod.fst |>.foldl (·+·) 0
  let actual_sum := result.filter (·.2 = item) |>.map Prod.fst |>.foldl (·+·) 0
  expected_sum = actual_sum :=
  sorry

theorem update_inventory_empty :
  List.update_inventory [] [] = [] :=
  sorry

theorem update_inventory_empty_plus_list (stock: List (Nat × String)) :
  List.update_inventory stock [] = List.update_inventory [] stock :=
  sorry

/-
info: []
-/
-- #guard_msgs in
-- #eval update_inventory [] []

/-
info: [(8, 'Apple')]
-/
-- #guard_msgs in
-- #eval update_inventory [(5, "Apple")] [(3, "Apple")]

/-
info: [(25, 'HTC'), (5, 'LG'), (1000, 'Nokia'), (54, 'Samsung')]
-/
-- #guard_msgs in
-- #eval update_inventory [(25, "HTC"), (1000, "Nokia"), (50, "Samsung")] [(5, "LG"), (4, "Samsung")]

-- Apps difficulty: introductory
-- Assurance level: unguarded