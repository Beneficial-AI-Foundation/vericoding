-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_smallest_k (n : Nat) (s : List Nat) : Int := sorry

def bxor (a b : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_smallest_k_positive (n : Nat) (s : List Nat) :
  let k := find_smallest_k n s
  k ≠ -1 → k > 0 := sorry

theorem find_smallest_k_bounded (n : Nat) (s : List Nat) :
  let k := find_smallest_k n s
  k ≠ -1 → k ≤ 1024 := sorry

theorem find_smallest_k_permutation_invariant (n : Nat) (s : List Nat) :
  s.length ≥ 2 → 
  find_smallest_k n s = find_smallest_k n s.reverse := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_smallest_k 4 [1, 0, 2, 3]

/-
info: 4
-/
-- #guard_msgs in
-- #eval find_smallest_k 6 [10, 7, 14, 8, 3, 12]

/-
info: 1023
-/
-- #guard_msgs in
-- #eval find_smallest_k 2 [0, 1023]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible