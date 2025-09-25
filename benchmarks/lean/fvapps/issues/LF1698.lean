-- <vc-preamble>
def fit_bag (height width : Nat) (items : List (List (List Nat))) : List (List Nat) := sorry

/- Each row in the result bag has the same width -/
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IsConnected (grid : List (List Nat)) (i j i' j' : Nat) : Prop := sorry

/- The items form connected shapes (no diagonals) -/
-- </vc-definitions>

-- <vc-theorems>
theorem fit_bag_uniform_width (height width : Nat) (items : List (List (List Nat))) 
  (result := fit_bag height width items) :
  ∀ row ∈ result, List.length row = width := sorry

/- Each number in the items appears exactly once in the result -/

theorem fit_bag_items_appear_once (height width : Nat) (items : List (List (List Nat))) 
  (result := fit_bag height width items) :
  ∀ item ∈ items, ∀ val : Nat,
    (val ∈ (List.join item) ∧ val ≠ 0) →
    (List.countP (λ x => x = val) (List.join result) = 
     List.countP (λ x => x = val) (List.join item)) := sorry

theorem fit_bag_items_connected (height width : Nat) (items : List (List (List Nat))) 
  (result := fit_bag height width items) :
  ∀ item ∈ items, ∀ val : Nat,
    val ∈ (List.join item) →
    val ≠ 0 → 
    ∀ i j i' j', 
      i < List.length item ∧ j < List.length (List.get! item i) ∧
      i' < List.length item ∧ j' < List.length (List.get! item i') ∧
      List.get! (List.get! item i) j = val ∧
      List.get! (List.get! item i') j' = val →
      IsConnected item i j i' j' := sorry

/- The result has the specified dimensions -/

theorem fit_bag_dimensions (height width : Nat) (items : List (List (List Nat))) 
  (result := fit_bag height width items) :
  List.length result = height ∧
  ∀ row ∈ result, List.length row = width := sorry

/- All numbers in result appear in original items -/

theorem fit_bag_valid_numbers (height width : Nat) (items : List (List (List Nat))) 
  (result := fit_bag height width items) :
  ∀ x ∈ List.join result,
    x = 0 ∨ ∃ item ∈ items, x ∈ List.join item := sorry
-- </vc-theorems>