-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_height_shelves (books : Books) (width : ShelfWidth) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_height_lower_bound_tallest (books : Books) (width : ShelfWidth)
  (h1 : books.length > 0)
  (h2 : width > 0) :
  min_height_shelves books width ≥ books.foldl (λ acc b => max acc b.height) 0 :=
sorry

theorem min_height_width_one_lower_bound (books : Books)
  (h1 : books.length > 0)
  (h2 : width = 1) :
  min_height_shelves books 1 ≥ books.foldl (λ acc b => acc + b.height) 0 :=
sorry

theorem min_height_upper_bound (books : Books) (width : ShelfWidth)
  (h1 : books.length > 0)
  (h2 : width > 0) :
  min_height_shelves books width ≤ books.foldl (λ acc b => acc + b.height) 0 :=
sorry

theorem min_height_monotonic_width (books : Books) (w1 w2 : ShelfWidth)
  (h1 : books.length > 0)
  (h2 : w1 > 0)
  (h3 : w2 = w1 + 1) :
  min_height_shelves books w2 ≤ min_height_shelves books w1 :=
sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval min_height_shelves [[1, 1], [2, 3], [2, 3], [1, 1], [1, 1], [1, 1], [1, 2]] 4

/-
info: 4
-/
-- #guard_msgs in
-- #eval min_height_shelves [[1, 3], [2, 4], [3, 2]] 6

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_height_shelves [[1, 1]] 1
-- </vc-theorems>