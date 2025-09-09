-- <vc-helpers>
-- </vc-helpers>

def trim (beard : List (List String)) : List (List String) := sorry

theorem trim_dimensions {beard : List (List String)} (h1 : beard.length ≥ 2) 
  (h2 : ∀ row ∈ beard, row.length ≥ 1) :
  let result := trim beard
  (result.length = beard.length) ∧ 
  (∀ row ∈ result, row.length = (beard.head!).length) := sorry

theorem trim_interior_rows {beard : List (List String)} (h1 : beard.length ≥ 2) 
  (h2 : ∀ row ∈ beard, row.length ≥ 1) :
  let result := trim beard
  ∀ i < result.length - 1, ∀ c ∈ result[i]!, c = "|" := sorry

theorem trim_last_row {beard : List (List String)} (h1 : beard.length ≥ 2)
  (h2 : ∀ row ∈ beard, row.length ≥ 1) :
  let result := trim beard
  ∀ c ∈ result.getLast!, c = "..." := sorry

theorem trim_idempotent {beard : List (List String)} (h1 : beard.length ≥ 2)
  (h2 : ∀ row ∈ beard, ∀ c ∈ row, c = "|") :
  trim (trim beard) = trim beard := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval trim [["J", "|"], ["J", "|"], ["...", "|"]]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval trim [["J", "|", "J"], ["J", "|", "|"], ["...", "|", "J"]]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval trim [["J", "|", "J", "J"], ["J", "|", "|", "J"], ["...", "|", "J", "|"]]

-- Apps difficulty: introductory
-- Assurance level: unguarded