-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numOfSubarrays (arr : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numsub_bound (arr : List Nat) (h : arr.length > 0) :
  numOfSubarrays arr < 10^9 + 7 ∧ numOfSubarrays arr ≥ 0 :=
  sorry

theorem all_even_zero (arr : List Nat) (h : arr.length > 0) :
  numOfSubarrays (arr.map (· * 2)) = 0 :=
  sorry

theorem parity_equivalent (arr : List Nat) (h : arr.length > 0) :
  numOfSubarrays arr = numOfSubarrays (arr.map (· % 2)) :=
  sorry

theorem reverse_invariant (arr : List Nat) (h : arr.length > 0) :
  numOfSubarrays arr = numOfSubarrays arr.reverse :=
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval numOfSubarrays [1, 3, 5]

/-
info: 0
-/
-- #guard_msgs in
-- #eval numOfSubarrays [2, 4, 6]

/-
info: 16
-/
-- #guard_msgs in
-- #eval numOfSubarrays [1, 2, 3, 4, 5, 6, 7]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded