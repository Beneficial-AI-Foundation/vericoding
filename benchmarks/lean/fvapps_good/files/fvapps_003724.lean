-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def micro_world (bacteria : List Nat) (k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem micro_world_bounds {bacteria : List Nat} (k : Nat) 
  (h : bacteria ≠ []) : 
  0 ≤ micro_world bacteria k ∧ micro_world bacteria k ≤ bacteria.length :=
  sorry

theorem micro_world_zero_k {bacteria : List Nat} :
  micro_world bacteria 0 = bacteria.length :=
  sorry

theorem micro_world_monotone {bacteria : List Nat} {k : Nat} 
  (h : k > 0) :
  micro_world bacteria k ≤ micro_world bacteria (k-1) :=
  sorry

theorem micro_world_same_size {bacteria : List Nat} {n k : Nat}
  (h : bacteria = List.replicate bacteria.length n) :
  micro_world bacteria k = bacteria.length :=
  sorry

theorem micro_world_edge_cases_empty (k : Nat) :
  micro_world [] k = 0 :=
  sorry

theorem micro_world_edge_cases_singleton (n k : Nat) :
  micro_world [n] k = 1 :=
  sorry
-- </vc-theorems>