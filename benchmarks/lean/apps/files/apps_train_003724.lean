-- <vc-helpers>
-- </vc-helpers>

def micro_world (bacteria : List Nat) (k : Nat) : Nat :=
  sorry

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

/-
info: 3
-/
-- #guard_msgs in
-- #eval micro_world [101, 53, 42, 102, 101, 55, 54] 1

/-
info: 1
-/
-- #guard_msgs in
-- #eval micro_world [20, 15, 10, 15, 20, 25] 5

/-
info: 4
-/
-- #guard_msgs in
-- #eval micro_world [5, 3, 1, 5] 1

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible