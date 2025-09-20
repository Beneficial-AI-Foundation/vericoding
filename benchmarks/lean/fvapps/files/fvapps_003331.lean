-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_red_beads (n : Nat) : Nat := sorry

theorem count_red_beads_non_negative (n : Nat) : 
  count_red_beads n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_red_beads_even (n : Nat) :
  count_red_beads n % 2 = 0 := sorry

theorem count_red_beads_edge_cases (n : Nat) (h : n ≤ 1) :
  count_red_beads n = 0 := sorry 

theorem count_red_beads_formula (n : Nat) (h : n ≥ 2) :
  count_red_beads n = 2 * (n - 1) := sorry
-- </vc-theorems>