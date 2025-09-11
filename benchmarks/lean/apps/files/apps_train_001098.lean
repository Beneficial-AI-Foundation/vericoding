-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reorder_dinosaurs (n : Nat) (k : Nat) : List Nat := sorry

theorem reorder_dinosaurs_k_swap {n k : Nat} (h : 0 < n) (hk : k < n) :
  List.get! (reorder_dinosaurs n k) k = n ∧ 
  List.get! (reorder_dinosaurs n k) (n-1) = k+1 := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: [1, 2, 5, 4, 3]
-/
-- #guard_msgs in
-- #eval reorder_dinosaurs 5 2

/-
info: [1, 4, 3, 2]
-/
-- #guard_msgs in
-- #eval reorder_dinosaurs 4 1

/-
info: [3, 2, 1]
-/
-- #guard_msgs in
-- #eval reorder_dinosaurs 3 0
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible