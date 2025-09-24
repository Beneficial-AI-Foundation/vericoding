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
-- </vc-theorems>