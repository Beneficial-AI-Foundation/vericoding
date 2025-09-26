-- <vc-preamble>
def List.sum : List Int → Int 
  | [] => 0
  | x::xs => x + sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def invite_more_women (arr : List Int) : Bool := sorry

theorem invite_more_women_sum_property (arr : List Int) 
  (h : arr.length > 0)
  (h₁ : ∀ x ∈ arr, x = 1 ∨ x = -1) :
  invite_more_women arr = (List.sum arr > 0) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem party_balance_monotonicity (arr : List Int)
  (h : arr.length > 0)
  (h₁ : ∀ x ∈ arr, x = 1 ∨ x = -1) :
  invite_more_women (arr ++ [-1]) ≤ invite_more_women arr ∧ 
  invite_more_women arr ≤ invite_more_women (arr ++ [1]) := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval invite_more_women [1, -1, 1]

/-
info: False
-/
-- #guard_msgs in
-- #eval invite_more_women [-1, -1, -1]

/-
info: False
-/
-- #guard_msgs in
-- #eval invite_more_women [1, -1]
-- </vc-theorems>