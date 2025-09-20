-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reorder (n : Nat) (m : Nat) : (List Nat × List Nat) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reorder_output_size {n m : Nat} (h : 2 ∣ n) (h2 : n ≥ 2) :
  let result := reorder n m
  List.length result.1 = n/2 ∧ List.length result.2 = n/2 :=
sorry

theorem reorder_partitions {n m : Nat} (h : 2 ∣ n) (h2 : n ≥ 2) :
  let result := reorder n m
  let flattened := result.1 ++ result.2
  List.Perm flattened (List.range n) :=
sorry

theorem reorder_mod_equiv {n m : Nat} (h : 2 ∣ n) (h2 : n ≥ 2) :
  reorder n m = reorder n (m % (n/2)) :=
sorry

theorem reorder_halves_bound {n m : Nat} (h : 2 ∣ n) (h2 : n ≥ 2) :
  let result := reorder n m
  (∀ x ∈ result.1, x < n/2) ∧ 
  (∀ x ∈ result.2, x ≥ n/2) :=
sorry
-- </vc-theorems>