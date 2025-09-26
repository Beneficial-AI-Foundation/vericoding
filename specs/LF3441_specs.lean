-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rotate {α : Type u} (arr : List α) (n : Int) : List α :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rotate_empty {α : Type u} (n : Int) :
  rotate ([] : List α) n = ([] : List α) :=
  sorry

theorem rotate_length {α : Type u} (arr : List α) (n : Int) :
  arr ≠ [] → List.length (rotate arr n) = List.length arr :=
  sorry

theorem rotate_elements_same {α : Type u} (arr : List α) (n : Int) (x : α) :
  arr ≠ [] → (x ∈ arr ↔ x ∈ rotate arr n) :=
  sorry

theorem rotate_period {α : Type u} (arr : List α) :
  arr ≠ [] → rotate arr (List.length arr) = arr :=
  sorry

theorem rotate_split {α : Type u} (arr : List α) (n : Int) :
  arr ≠ [] →
  let normalized := Int.mod n (List.length arr)
  rotate arr n = arr.drop (List.length arr - normalized.toNat) ++ arr.take (List.length arr - normalized.toNat) :=
  sorry

theorem rotate_compose {α : Type u} (arr : List α) (n1 n2 : Int) :
  arr ≠ [] →
  rotate (rotate arr n1) n2 = rotate arr (Int.mod (n1 + n2) (List.length arr)) :=
  sorry

theorem rotate_inverse {α : Type u} (arr : List α) (n : Int) :
  arr ≠ [] →
  rotate (rotate arr n) (-n) = arr :=
  sorry

/-
info: ['c', 'a', 'b']
-/
-- #guard_msgs in
-- #eval rotate ["a", "b", "c"] 1

/-
info: [3.0, 1.0, 2.0]
-/
-- #guard_msgs in
-- #eval rotate [1.0, 2.0, 3.0] 1

/-
info: [False, True, True]
-/
-- #guard_msgs in
-- #eval rotate [True, True, False] 1

/-
info: [4, 5, 1, 2, 3]
-/
-- #guard_msgs in
-- #eval rotate [1, 2, 3, 4, 5] 7
-- </vc-theorems>