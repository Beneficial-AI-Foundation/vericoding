def are_similar (xs ys : List Int) : Bool := sorry

theorem identical_lists_are_similar {xs : List Int} (h : xs ≠ []) : 
  are_similar xs xs := sorry

-- <vc-helpers>
-- </vc-helpers>

def insertSort (xs : List Int) : List Int := sorry 

theorem different_contents_not_similar {xs ys : List Int} :
  insertSort xs ≠ insertSort ys →
  ¬(are_similar xs ys) := sorry

theorem single_swap_makes_similar {xs : List Int} (h : xs.length ≥ 2) :
  let ys := xs.set 0 (xs.get! 1) |>.set 1 (xs.get! 0)
  are_similar xs ys := sorry

theorem multiple_swaps_not_similar {xs : List Int} (h : xs.length ≥ 3) :
  let ys := xs.set 0 (xs.get! 1)
            |>.set 1 (xs.get! 2)
            |>.set 2 (xs.get! 0)
  (List.length (List.filter (fun p => p.1 ≠ p.2) (List.zip xs ys))) > 2 →
  ¬(are_similar xs ys) := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval are_similar [1, 2, 3] [1, 2, 3]

/-
info: True
-/
-- #guard_msgs in
-- #eval are_similar [1, 2, 3] [2, 1, 3]

/-
info: False
-/
-- #guard_msgs in
-- #eval are_similar [1, 2, 2] [2, 1, 1]

-- Apps difficulty: introductory
-- Assurance level: unguarded