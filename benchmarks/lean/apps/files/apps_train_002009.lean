-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_permutation (n k : Nat) : List Nat := sorry

def count_differences (arr : List Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_perm_length (n k : Nat) (h1 : n ≥ 2) (h2 : k ≥ 1) (h3 : k ≤ n-1) :
  List.length (find_permutation n k) = n := sorry

theorem find_perm_contains_all (n k : Nat) (h1 : n ≥ 2) (h2 : k ≥ 1) (h3 : k ≤ n-1) (i : Nat) (hi : i < n) :
  i + 1 ∈ find_permutation n k := sorry

theorem find_perm_k_one (n : Nat) (h : n ≥ 1) :
  find_permutation n 1 = List.range n := sorry

theorem find_perm_edge_cases :
  find_permutation 1 1 = [1] ∧ 
  find_permutation 5 1 = [1,2,3,4,5] := sorry

theorem find_perm_three_two :
  count_differences (find_permutation 3 2) = 2 := sorry

/-
info: [1, 3, 2]
-/
-- #guard_msgs in
-- #eval find_permutation 3 2

/-
info: [1, 2, 3]
-/
-- #guard_msgs in
-- #eval find_permutation 3 1

/-
info: [1, 3, 2, 4, 5]
-/
-- #guard_msgs in
-- #eval find_permutation 5 2
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded