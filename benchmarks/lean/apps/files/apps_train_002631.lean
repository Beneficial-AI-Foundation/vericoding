-- <vc-helpers>
-- </vc-helpers>

def find_abc_sumsqcube (c_max : Nat) (num_sol : Nat) : List Nat := sorry

theorem find_abc_sumsqcube_sorted (c_max : Nat) (num_sol : Nat) :
  let result := find_abc_sumsqcube c_max num_sol
  List.Pairwise (fun x y => x ≤ y) result := sorry

/-
info: [2]
-/
-- #guard_msgs in
-- #eval find_abc_sumsqcube 5 1

/-
info: [5]
-/
-- #guard_msgs in
-- #eval find_abc_sumsqcube 5 2

/-
info: [5, 10]
-/
-- #guard_msgs in
-- #eval find_abc_sumsqcube 10 2

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible