def sum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x::xs => x + sum xs

-- <vc-helpers>
-- </vc-helpers>

def save (sizes : List Nat) (hd : Nat) : Nat :=
  sorry

theorem save_valid_result_range (sizes : List Nat) (hd : Nat) (h : sizes.length > 0) :
  let result := save sizes hd
  0 ≤ result ∧ result ≤ sizes.length :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval save [4, 4, 4, 3, 3] 12

/-
info: 2
-/
-- #guard_msgs in
-- #eval save [4, 4, 4, 3, 3] 11

/-
info: 6
-/
-- #guard_msgs in
-- #eval save [4, 8, 15, 16, 23, 42] 108

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible