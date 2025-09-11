-- <vc-preamble>
def est_subsets {α : Type} [BEq α] [Hashable α] (arr : List α) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_unique_count {α : Type} [BEq α] [Hashable α] (arr : List α) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem est_subsets_count_prop {α : Type} [BEq α] [Hashable α] (arr : List α) :
  est_subsets arr = 2^(list_unique_count arr) - 1 :=
  sorry

theorem est_subsets_nonneg {α : Type} [BEq α] [Hashable α] (arr : List α) :
  est_subsets arr ≥ 0 :=
  sorry

theorem est_subsets_empty {α : Type} [BEq α] [Hashable α] :
  est_subsets ([] : List α) = 0 :=
  sorry

theorem est_subsets_duplicates {α : Type} [BEq α] [Hashable α] (arr : List α) :
  est_subsets arr = est_subsets (arr ++ arr) :=
  sorry

theorem est_subsets_is_nat {α : Type} [BEq α] [Hashable α] (arr : List α) :
  est_subsets arr = 2^(list_unique_count arr) - 1 :=
  sorry

/-
info: 15
-/
-- #guard_msgs in
-- #eval est_subsets [1, 2, 3, 4]

/-
info: 15
-/
-- #guard_msgs in
-- #eval est_subsets ["a", "b", "c", "d", "d"]

/-
info: 15
-/
-- #guard_msgs in
-- #eval est_subsets [1, 2, 2, 3, 3, 3, 4]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded