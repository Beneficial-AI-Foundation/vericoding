-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_minimal_goodness (n h : Nat) (a : List Nat) : Nat × List Nat := sorry

theorem solve_minimal_goodness_returns_valid_types {n h : Nat} {a : List Nat} 
  (hn : n ≥ 2) : (solve_minimal_goodness n h a).2.length = n ∧ 
                  (solve_minimal_goodness n h a).1 ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_minimal_goodness_partition_values {n h : Nat} {a : List Nat}
  (hn : n ≥ 2) : (solve_minimal_goodness n h a).2.all (fun x => x = 1 ∨ x = 2) := sorry

theorem solve_minimal_goodness_n2_case {h : Nat} {a : List Nat} :
  solve_minimal_goodness 2 h a = (0, [1,1]) := sorry

theorem solve_minimal_goodness_sorted_invariant {n h : Nat} {a sorted_a : List Nat}
  (hn : n ≥ 3) : (solve_minimal_goodness n h a).1 = 
                  (solve_minimal_goodness n h sorted_a).1 := sorry
-- </vc-theorems>