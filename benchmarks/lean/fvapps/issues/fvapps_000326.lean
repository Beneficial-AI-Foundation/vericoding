-- <vc-preamble>
def List.sum : List Int → Int 
  | [] => 0
  | x::xs => x + sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.sort (xs : List Int) : List Int := sorry

def tallestBillboard (rods: List Int) : Int := sorry

/- The result of tallestBillboard is non-negative -/
-- </vc-definitions>

-- <vc-theorems>
theorem tallestBillboard_nonneg {rods: List Int}
  (h: ∀ x ∈ rods, x > 0) : 
  tallestBillboard rods ≥ 0 := sorry

/- The result cannot exceed half the sum of all rods -/

theorem tallestBillboard_upper_bound {rods: List Int}
  (h: ∀ x ∈ rods, x > 0) :
  2 * tallestBillboard rods ≤ List.sum rods := sorry

/- The result is invariant under sorting -/

theorem tallestBillboard_sort_invariant {rods: List Int}
  (h: ∀ x ∈ rods, x > 0) :
  tallestBillboard rods = tallestBillboard (List.sort rods) := sorry

/- Empty input results in 0 -/

theorem tallestBillboard_empty :
  tallestBillboard [] = 0 := sorry

/- Single input results in 0 -/

theorem tallestBillboard_singleton (x: Int)
  (h: x > 0) :
  tallestBillboard [x] = 0 := sorry

/- For input of length 2, result is input value if equal, 0 otherwise -/

theorem tallestBillboard_pair (x y: Int)
  (hx: x > 0) (hy: y > 0) :
  tallestBillboard [x, y] = (if x = y then x else 0) := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval tallestBillboard [1, 2, 3, 6]

/-
info: 10
-/
-- #guard_msgs in
-- #eval tallestBillboard [1, 2, 3, 4, 5, 6]

/-
info: 0
-/
-- #guard_msgs in
-- #eval tallestBillboard [1, 2]
-- </vc-theorems>