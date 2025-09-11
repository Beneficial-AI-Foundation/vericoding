-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_last (n m : Nat) : Nat × Nat := sorry

theorem result_format {n m : Nat} (hn : n ≥ 2) (hm : m ≥ 1) :
  let (player, coins) := find_last n m
  player ≥ 1 ∧ player ≤ n ∧ coins ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem m_equals_one {n : Nat} (hn : n ≥ 2) :
  (find_last n 1).1 = n := sorry

theorem coins_increase {n1 n2 m : Nat} (h1 : n1 ≥ 2) (h2 : n2 > n1) (hm : m ≥ 1) :
  (find_last n1 m).2 < (find_last n2 m).2 := sorry

/-
info: (5, 24)
-/
-- #guard_msgs in
-- #eval find_last 5 1

/-
info: (7, 51)
-/
-- #guard_msgs in
-- #eval find_last 8 3

/-
info: (35, 4238)
-/
-- #guard_msgs in
-- #eval find_last 75 34
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded