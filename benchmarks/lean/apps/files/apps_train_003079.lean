-- <vc-helpers>
-- </vc-helpers>

def true_binary (n : Nat) : List Int := sorry

theorem true_binary_starts_with_one {n : Nat} (h : n % 2 = 1) :
  match true_binary n with
  | [] => False 
  | x::xs => x = 1
  := sorry

theorem true_binary_elements_are_ones {n : Nat} (h : n % 2 = 1) :
  ∀ x ∈ true_binary n, x = 1 ∨ x = -1 := sorry

theorem true_binary_length {n : Nat} (h : n % 2 = 1) :
  List.length (true_binary n) = Nat.log2 n := sorry

/-
info: [1, 1, 1, -1, -1]
-/
-- #guard_msgs in
-- #eval true_binary 25

/-
info: [1, 1, -1, 1, 1, 1]
-/
-- #guard_msgs in
-- #eval true_binary 47

/-
info: [1]
-/
-- #guard_msgs in
-- #eval true_binary 1

-- Apps difficulty: introductory
-- Assurance level: unguarded