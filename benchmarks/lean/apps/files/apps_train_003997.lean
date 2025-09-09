-- <vc-helpers>
-- </vc-helpers>

def every (lst: List α) (n: Nat := 1) (start: Nat := 0) : List α := sorry

theorem every_is_subset {α : Type} (lst : List α) (n: Nat) (start: Nat) 
  (h: start < lst.length) :
  ∀ x ∈ every lst n start, x ∈ lst := sorry

theorem every_indices_pattern {α : Type} (lst : List α) (n: Nat) (start: Nat)
  (h: start < lst.length) (x : α) (i : Nat) (hi: i < lst.length) :
  x ∈ every lst n start → 
  lst.get ⟨i, hi⟩ = x →
  (i - start) % n = 0 := sorry

theorem every_default_start {α : Type} (lst : List α) (n: Nat) :
  every lst n = every lst n 0 := sorry

theorem every_one_full_slice {α : Type} (lst : List α) (start: Nat)
  (h: 0 < lst.length) :
  every lst 1 start = lst.drop start := sorry

/-
info: [1, 3, 5]
-/
-- #guard_msgs in
-- #eval every [1, 2, 3, 4, 5] 2

/-
info: [2, 4]
-/
-- #guard_msgs in
-- #eval every [1, 2, 3, 4, 5] 2 1

/-
info: [1, 2, 3]
-/
-- #guard_msgs in
-- #eval every [1, 2, 3]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible