-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_product (lst : List Int) (n : Nat) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_product_single_equals_maximum {lst : List Int} 
  (h : lst.length > 0) :
  ∃ m ∈ lst, (max_product lst 1 = m ∧ ∀ x ∈ lst, x ≤ m) :=
  sorry

theorem max_product_full_list {lst : List Int}
  (h : lst.length > 0) :
  max_product lst lst.length = List.foldl (· * ·) 1 lst :=
  sorry

theorem max_product_singleton_positive :
  max_product [1] 1 = 1 :=
  sorry

theorem max_product_singleton_negative :
  max_product [-1] 1 = -1 :=
  sorry

theorem max_product_singleton_zero :
  max_product [0] 1 = 0 :=
  sorry

/-
info: 20
-/
-- #guard_msgs in
-- #eval max_product [4, 3, 5] 2

/-
info: 720
-/
-- #guard_msgs in
-- #eval max_product [10, 8, 7, 9] 3

/-
info: 4
-/
-- #guard_msgs in
-- #eval max_product [-4, -27, -15, -6, -1] 2
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible