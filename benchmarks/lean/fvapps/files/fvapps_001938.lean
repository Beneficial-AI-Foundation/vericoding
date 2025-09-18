-- <vc-preamble>
def find_min_sum_permutation (n : Nat) : List Nat := sorry

def abs (n : Nat) (m : Nat) : Nat :=
  if n ≥ m then n - m else m - n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSortedList : List Nat → Bool
  | [] => true
  | [_] => true
  | x :: y :: xs => x ≤ y && isSortedList (y :: xs)
-- </vc-definitions>

-- <vc-theorems>
theorem permutation_length {n : Nat} (h : 0 < n) (h2 : n ≤ 1000) : 
  let result := find_min_sum_permutation n
  List.length result = n ∧ 
  isSortedList result := sorry

theorem sum_property {n : Nat} (h : 0 < n) (h2 : n ≤ 1000) :
  let result := find_min_sum_permutation n
  let pairs := List.zip (List.take (List.length result - 1) result) (List.drop 1 result)
  let cumsum := List.foldl (fun acc (p : Nat × Nat) => acc + abs p.1 p.2) 0 pairs
  let rev := List.reverse result
  let rev_pairs := List.zip (List.take (List.length rev - 1) rev) (List.drop 1 rev)
  let rev_sum := List.foldl (fun acc (p : Nat × Nat) => acc + abs p.1 p.2) 0 rev_pairs
  cumsum ≤ rev_sum := sorry

/-
info: [3, 4, 1, 2]
-/
-- #guard_msgs in
-- #eval find_min_sum_permutation 4

/-
info: [2, 1]
-/
-- #guard_msgs in
-- #eval find_min_sum_permutation 2

/-
info: [3, 2, 1]
-/
-- #guard_msgs in
-- #eval find_min_sum_permutation 3
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: guarded