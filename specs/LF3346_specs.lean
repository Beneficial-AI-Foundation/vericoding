-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def any_arrows (arrows : List Arrow) : Bool := sorry

theorem any_arrows_all_damaged 
  (arrows : List Arrow)
  (h : ∀ a ∈ arrows, (a.damaged = some true)) :
  any_arrows arrows = false := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem any_arrows_exists_undamaged
  (arrows : List Arrow)
  (h : ∃ a ∈ arrows, (a.damaged = some false) ∨ (a.damaged = none)) :
  any_arrows arrows = true := sorry

theorem any_arrows_empty :
  any_arrows [] = false := sorry

theorem any_arrows_undamaged_only
  (arrows : List Arrow)
  (h : ∀ a ∈ arrows, a.damaged = none) :
  any_arrows arrows = (arrows ≠ []) := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval any_arrows []

/-
info: True
-/
-- #guard_msgs in
-- #eval any_arrows [{"range": 5}]

/-
info: True
-/
-- #guard_msgs in
-- #eval any_arrows [{"range": 5}, {"range": 10, "damaged": True}, {"damaged": True}]
-- </vc-theorems>