-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_time_tasks (n : Nat) (difficulties : List Nat) : Nat := sorry

theorem min_time_tasks_modulo_bounds {n : Nat} {difficulties : List Nat} 
  (h : difficulties.length = n) (h1 : n > 0) : 
  min_time_tasks n difficulties < 10007 ∧ min_time_tasks n difficulties ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_time_tasks_permutation_invariant {n : Nat} {d1 d2 : List Nat} 
  (h : d1.length = n) (h2 : d2.length = n) (h3 : d1 = d2) :
  min_time_tasks n d1 = min_time_tasks n d2 := sorry

theorem min_time_tasks_two_elements_commutative (a b : Nat) :
  min_time_tasks 2 [a, b] = min_time_tasks 2 [b, a] := sorry

theorem min_time_tasks_two_elements_bounds (a b : Nat) 
  (h1 : a > 0) (h2 : b > 0) (h3 : a ≤ 100) (h4 : b ≤ 100) :
  min_time_tasks 2 [a, b] < 10007 ∧ min_time_tasks 2 [a, b] ≥ 0 := sorry
-- </vc-theorems>