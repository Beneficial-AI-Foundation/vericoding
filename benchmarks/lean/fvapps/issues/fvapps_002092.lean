-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_pairs (n: Nat) : List (Nat × Nat) := sorry

theorem find_max_pairs_range {n: Nat} (h: n ≥ 2) :
  let result := find_max_pairs n
  let flat_nums := result.bind (λ p => [p.1, p.2])
  ∀ x ∈ flat_nums, 1 ≤ x ∧ x ≤ n := 
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_max_pairs_unique {n: Nat} (h: n ≥ 2) :
  let result := find_max_pairs n
  let flat_nums := result.bind (λ p => [p.1, p.2])
  ∀ x ∈ flat_nums, ∀ y ∈ flat_nums, x ≠ y → 
    flat_nums.indexOf x ≠ flat_nums.indexOf y :=
sorry

/-
info: expected_groups
-/
-- #guard_msgs in
-- #eval len find_max_pairs(n)

/-
info: 2
-/
-- #guard_msgs in
-- #eval len pair
-- </vc-theorems>