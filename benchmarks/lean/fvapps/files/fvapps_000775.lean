-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def assign_bowlers (n k l : Nat) : List Nat := sorry

theorem assign_bowlers_properties {n k l : Nat} (h1 : n > 0) (h2 : k > 0) (h3 : l > 0) :
  let result := assign_bowlers n k l
  (result = List.nil → (k * l < n ∨ (k = 1 ∧ n > 1))) ∧
  (result ≠ List.nil → 
    (result.length = n) ∧
    (∀ x ∈ result, 1 ≤ x ∧ x ≤ k) ∧
    (∀ i : Fin (n-1), result[i.val]! ≠ result[i.val + 1]!) ∧
    (∀ i : Fin k, (result.count (i.val + 1)) ≤ l)
  ) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_bowler_case (k l : Nat) (h1 : k > 0) (h2 : l > 0) :
  assign_bowlers 1 k l = [1] := sorry 

theorem impossible_single_bowler (n : Nat) (h : n ≥ 2) :
  assign_bowlers n 1 n = List.nil := sorry

theorem capacity_constraint (n k l : Nat) (h1 : n > 0) (h2 : k > 0) (h3 : l > 0) :
  k * l < n → assign_bowlers n k l = List.nil := sorry
-- </vc-theorems>