/-
Write a function `reverse` which reverses a list (or in clojure's case, any list-like data structure)

(the dedicated builtin(s) functionalities are deactivated)
-/

-- <vc-helpers>
-- </vc-helpers>

def reverse {α : Type} : List α → List α := sorry

theorem reverse_length_preserves {α : Type} (lst : List α) : 
  (reverse lst).length = lst.length := sorry

theorem reverse_involutive {α : Type} (lst : List α) : 
  reverse (reverse lst) = lst := sorry

theorem reverse_empty {α : Type} : 
  reverse ([] : List α) = [] := sorry

theorem reverse_eq_manual {α : Type} (lst : List α) :
  ∃ manual_reverse : List α → List α, 
    reverse lst = manual_reverse lst := sorry

/-
info: [5, 4, 3, 2, 1]
-/
-- #guard_msgs in
-- #eval reverse [1, 2, 3, 4, 5]

/-
info: ['c', 'b', 'a']
-/
-- #guard_msgs in
-- #eval reverse ["a", "b", "c"]

/-
info: []
-/
-- #guard_msgs in
-- #eval reverse []

-- Apps difficulty: introductory
-- Assurance level: unguarded