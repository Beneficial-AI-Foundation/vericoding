-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check (lst : List Int) (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_non_negative (lst : List Int) (n : Nat) :
  check lst n ≥ 0 :=
sorry

theorem check_empty_or_singleton (lst : List Int) (n : Nat) :
  n ≤ 1 → check lst n = 0 :=
sorry

theorem check_unique_elements (lst : List Int) :
  List.Nodup lst → check lst lst.length = 0 :=
sorry

theorem check_all_same {n : Nat} {a : Int} :
  n ≥ 3 → 
  let lst := List.replicate n a
  check lst n > 0 :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval check [6, 3, 6, 4, 5, 4, 3, 6] len(test1)

/-
info: 2
-/
-- #guard_msgs in
-- #eval check [5, 5, 4, 5, 2, 1, 3, 4, 2] len(test2)

/-
info: 0
-/
-- #guard_msgs in
-- #eval check [1, 2, 3, 4, 5, 6] len(test3)
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded