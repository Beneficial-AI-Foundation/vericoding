def unique_sum (lst: List Int) : Option Int := sorry

def listToSet (lst: List Int) : List Int := sorry

-- <vc-helpers>
-- </vc-helpers>

def listSum (lst: List Int) : Int :=
  lst.foldl (· + ·) 0

theorem unique_sum_properties (lst : List Int) :
  match lst with
  | [] => unique_sum lst = none  
  | _  => unique_sum lst = some (listSum (listToSet lst))
  := sorry

theorem unique_sum_nonempty {lst : List Int} (h : lst ≠ []) :
  ∃ n : Int, unique_sum lst = some n ∧ n = listSum (listToSet lst) := sorry

theorem unique_sum_duplicates {lst : List Int} (h : lst ≠ []) 
  (h2 : ∀ x ∈ lst, x ≠ 0) :
  unique_sum (lst ++ lst) = unique_sum lst := sorry

/-
info: None
-/
-- #guard_msgs in
-- #eval unique_sum []

/-
info: 6
-/
-- #guard_msgs in
-- #eval unique_sum [1, 2, 3]

/-
info: 12
-/
-- #guard_msgs in
-- #eval unique_sum [1, 3, 8, 1, 8]

-- Apps difficulty: introductory
-- Assurance level: unguarded