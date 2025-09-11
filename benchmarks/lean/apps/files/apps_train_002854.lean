-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_pronic (n : Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pronic_exists_k {n : Int} (h : is_pronic n) : 
  ∃ k : Int, k * (k + 1) = n :=
  sorry

theorem negative_not_pronic {n : Int} (h : n < 0) :
  ¬ is_pronic n :=
  sorry

theorem consecutive_product_is_pronic (n : Int) (h : n ≥ 0) :
  is_pronic (n * (n + 1)) :=
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_pronic 2

/-
info: False
-/
-- #guard_msgs in
-- #eval is_pronic 3

/-
info: False
-/
-- #guard_msgs in
-- #eval is_pronic -3
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded