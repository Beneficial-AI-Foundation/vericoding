-- <vc-helpers>
-- </vc-helpers>

def solve_wire_problem (n m : Nat) : Int := sorry

theorem valid_n_range {n : Nat} (h : 1 ≤ n ∧ n ≤ 30) :
  let m := n * n;
  -1 ≤ solve_wire_problem n m := sorry

theorem output_ranges {n m : Nat} (hn : 1 ≤ n ∧ n ≤ 30) (hm : m ≤ 1000) :
  solve_wire_problem n m = -1 ∨ 0 ≤ solve_wire_problem n m := sorry

theorem insufficient_wire_negative {n : Nat} (h : 1 ≤ n ∧ n ≤ 30) :
  solve_wire_problem n 1 = -1 := sorry

theorem monotonic_extra {n : Nat} (h : 1 ≤ n ∧ n ≤ 30) :
  ∀ m₁ m₂, n*2 ≤ m₁ → m₁ ≤ m₂ → m₂ ≤ n*n*2 →
  0 ≤ solve_wire_problem n m₁ → 0 ≤ solve_wire_problem n m₂ →
  solve_wire_problem n m₁ ≤ solve_wire_problem n m₂ := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_wire_problem 3 8

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_wire_problem 3 9

/-
info: -1
-/
-- #guard_msgs in
-- #eval solve_wire_problem 2 4

/-
info: 5
-/
-- #guard_msgs in
-- #eval solve_wire_problem 5 25

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible