-- <vc-preamble>
def reverse_list (xs : List α) : List α := sorry
def sum_list (xs : List Int) : Int := sorry

def head_of_list (xs : List α) : Option α := sorry

theorem reverse_length {α : Type} (xs : List α) :
  (reverse_list xs).length = xs.length := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.sum : List Int → Int
  | [] => 0 
  | x::xs => x + List.sum xs
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_correct {α : Type} (xs : List α) :
  reverse_list xs = xs.reverse := sorry

theorem reverse_involution {α : Type} (xs : List α) :
  reverse_list (reverse_list xs) = xs := sorry

theorem sum_list_correct (xs : List Int) :
  sum_list xs = List.sum xs := sorry

theorem sum_list_double (xs : List Int) :
  sum_list (xs ++ xs) = sum_list xs * 2 := sorry

theorem sum_list_nil :
  sum_list [] = 0 := sorry

theorem head_of_list_nonempty {α : Type} (xs : List α) (h : xs ≠ []) :
  head_of_list xs = xs.head? := sorry

theorem head_of_list_empty {α : Type} :
  head_of_list ([] : List α) = none := sorry

/-
info: [3, 2, 1]
-/
-- #guard_msgs in
-- #eval reverse_list [1, 2, 3]

/-
info: []
-/
-- #guard_msgs in
-- #eval reverse_list []

/-
info: 10
-/
-- #guard_msgs in
-- #eval sum_list [1, 2, 3, 4]

/-
info: 0
-/
-- #guard_msgs in
-- #eval sum_list []

/-
info: 1
-/
-- #guard_msgs in
-- #eval head_of_list [1, 2, 3]
-- </vc-theorems>