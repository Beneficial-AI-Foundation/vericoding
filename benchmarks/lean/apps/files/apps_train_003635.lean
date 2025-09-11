-- <vc-preamble>
def build_square (blocks: List Nat) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_sum : List Nat → Nat 
  | [] => 0
  | x::xs => x + list_sum xs
-- </vc-definitions>

-- <vc-theorems>
theorem sum_16_if_buildable {blocks : List Nat} :
  build_square blocks = true → 
  list_sum blocks ≥ 16 :=
sorry

theorem input_unchanged {blocks : List Nat} :
  build_square blocks = b →
  blocks = blocks :=
sorry

theorem invalid_pieces {blocks : List Nat} : 
  (∀ x ∈ blocks, x < 1 ∨ x > 4) →
  build_square blocks = false :=
sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval build_square [1, 1, 1, 1, 1, 1, 1, 2, 3, 4]

/-
info: False
-/
-- #guard_msgs in
-- #eval build_square [1, 3, 2, 4, 3, 3, 2]

/-
info: True
-/
-- #guard_msgs in
-- #eval build_square [4, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded