def solve_carrot_game (n : Nat) (A : List Nat) : List Nat := sorry

abbrev min' (a b : Nat) : Nat := if a ≤ b then a else b

-- <vc-helpers>
-- </vc-helpers>

def list_maximum (l : List Nat) : Nat :=
match l with
| [] => 0
| x::xs => List.foldl Nat.max x xs

theorem carrot_game_output_length {n : Nat} {A : List Nat} 
  (h : A.length > 0) (h2 : A.length = n) :
  (solve_carrot_game n A).length = n := sorry

theorem carrot_game_max_preserved {n : Nat} {A : List Nat} 
  (h : A.length > 0) (h2 : A.length = n) :
  list_maximum (solve_carrot_game n A) = list_maximum A := sorry

theorem carrot_game_elements_valid {n : Nat} {A : List Nat} 
  (h : A.length > 0) (h2 : A.length = n) :
  ∀ x ∈ (solve_carrot_game n A), 
    x ∈ A ∨ ∃ (i : Fin (A.length - 1)), 
      x = min' (A[i]) (A[i.val + 1]) := sorry

theorem carrot_game_identical_elements {n : Nat} {A : List Nat} 
  (h : A.length > 0) (h2 : A.length = n)
  (h3 : ∀ x ∈ A, x = 5) :
  ∀ x ∈ (solve_carrot_game n A), x = 5 := sorry

theorem carrot_game_last_element_is_max {n : Nat} {A : List Nat}
  (h : A.length > 0) (h2 : A.length = n) :
  List.getLast! (solve_carrot_game n A) = list_maximum A := sorry

/-
info: [3, 3, 5, 5]
-/
-- #guard_msgs in
-- #eval solve_carrot_game 4 [1, 2, 3, 5]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval solve_carrot_game 5 [1000000000, 1000000000, 1000000000, 1000000000, 1]

/-
info: [2, 8, 8]
-/
-- #guard_msgs in
-- #eval solve_carrot_game 3 [2, 8, 2]

-- Apps difficulty: competition
-- Assurance level: unguarded