-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def proper_fractions (n: Nat) : Nat := sorry

def count_coprime_nums (n: Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem proper_fractions_matches_count (n: Nat) (h: n ≥ 1) :
  proper_fractions n = count_coprime_nums n := sorry

theorem proper_fractions_bounds (n: Nat) (h: n ≥ 2) :
  proper_fractions n < n ∧ proper_fractions n ≥ 0 := sorry

theorem proper_fractions_one :
  proper_fractions 1 = 0 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval proper_fractions 1

/-
info: 8
-/
-- #guard_msgs in
-- #eval proper_fractions 15

/-
info: 20
-/
-- #guard_msgs in
-- #eval proper_fractions 25
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded