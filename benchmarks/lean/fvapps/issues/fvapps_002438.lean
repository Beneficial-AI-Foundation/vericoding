-- <vc-preamble>
def List.size {α} : List α → Nat 
  | [] => 0
  | (_::xs) => 1 + xs.size
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def computeProduct {α} (xs : List α) (ys : List β) : List (α × β) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem computeProduct_matches_itertools {α} (xs : List α) (ys : List β) 
  (h1 : xs.size > 0) (h2 : xs.size ≤ 10)
  (h3 : ys.size > 0) (h4 : ys.size ≤ 10) :
  computeProduct xs ys = List.join (xs.map (λ x => ys.map (λ y => (x, y)))) :=
sorry

/-
info: '(1, 3) (1, 4) (2, 3) (2, 4)'
-/
-- #guard_msgs in
-- #eval compute_product [1, 2] [3, 4]

/-
info: '(1, 3) (1, 4) (1, 5)'
-/
-- #guard_msgs in
-- #eval compute_product [1] [3, 4, 5]

/-
info: '(1, 4) (2, 4) (3, 4)'
-/
-- #guard_msgs in
-- #eval compute_product [1, 2, 3] [4]
-- </vc-theorems>