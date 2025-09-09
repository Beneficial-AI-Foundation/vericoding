-- <vc-helpers>
-- </vc-helpers>

def count_love_graphs (n m : Nat) : Nat := sorry

theorem count_love_graphs_mod (n m : Nat) (h1 : n ≥ 1) (h2 : m ≥ 0) :
  count_love_graphs n m < 1000000007 := sorry

theorem count_love_graphs_nonneg (n m : Nat) (h1 : n ≥ 1) (h2 : m ≥ 0) :
  count_love_graphs n m ≥ 0 := sorry

theorem count_love_graphs_base_case (m : Nat) :
  count_love_graphs 1 m = if m = 0 then 1 else 0 := sorry

theorem count_love_graphs_single_edge (n : Nat) (h : n ≥ 2) :
  count_love_graphs n 1 = (n * (n-1)) % 1000000007 := sorry

theorem count_love_graphs_small_values :
  count_love_graphs 2 1 = 2 ∧ 
  count_love_graphs 3 1 = 6 ∧ 
  count_love_graphs 2 2 = 2 := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_love_graphs 2 1

/-
info: 12
-/
-- #guard_msgs in
-- #eval count_love_graphs 3 2

/-
info: 12
-/
-- #guard_msgs in
-- #eval count_love_graphs 4 1

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible