-- <vc-helpers>
-- </vc-helpers>

def make_sequences (n : Nat) : Nat := sorry 

abbrev sum_list : List Nat → Nat 
  | [] => 0
  | (x::xs) => x + sum_list xs

theorem count_at_least_one (n : Nat) (h: n > 0) : 
  make_sequences n ≥ 1 := sorry

theorem deterministic (n : Nat) (h: n > 0) :
  make_sequences n = make_sequences n := sorry

theorem monotonic_up_to_n (n : Nat) (h: n > 1) :
  make_sequences n ≥ make_sequences (n-1) := sorry

theorem recursive_relation (n : Nat) (h: n > 0) :
  make_sequences n = 1 + sum_list (List.map make_sequences (List.range (n/2))) := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval make_sequences 6

/-
info: 14
-/
-- #guard_msgs in
-- #eval make_sequences 10

/-
info: 1981471878
-/
-- #guard_msgs in
-- #eval make_sequences 1000

-- Apps difficulty: introductory
-- Assurance level: unguarded