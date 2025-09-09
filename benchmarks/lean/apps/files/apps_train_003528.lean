-- <vc-helpers>
-- </vc-helpers>

def Value := String ⊕ Int

def unusual_sort (arr : List Value) : List Value :=
  sorry

theorem unusual_sort_preserves_length (arr : List Value) :
  (unusual_sort arr).length = arr.length :=
  sorry

theorem unusual_sort_preserves_elements (arr : List Value) :
  ∃ perm : List.Perm (unusual_sort arr) arr,
    ∀ x, x ∈ unusual_sort arr ↔ x ∈ arr :=
  sorry

/-
info: ['a', 'b', 'c', 1, '2', 3]
-/
-- #guard_msgs in
-- #eval unusual_sort [3, "2", 1, "a", "c", "b"]

/-
info: [1, '1', 2, '2', 3, '3']
-/
-- #guard_msgs in
-- #eval unusual_sort [3, "3", "2", 2, "1", 1]

/-
info: ['a', 'b', 'c', '0', '5', '9']
-/
-- #guard_msgs in
-- #eval unusual_sort ["c", "b", "a", "9", "5", "0"]

-- Apps difficulty: introductory
-- Assurance level: unguarded