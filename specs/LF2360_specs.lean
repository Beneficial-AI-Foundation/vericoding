-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_deletion_size (strings : List String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_deletion_sorted_cols_zero 
  (strings : List String)
  (h1 : strings.length > 1)
  (h2 : ∀ (i j : Nat), i < strings.length → j < strings.length → 
    strings[i]!.length = strings[j]!.length)
  (h3 : ∀ (col : Nat) (hcol: col < strings[0]!.length), 
    ∀ (i j : Nat) (hi : i < strings.length) (hj : j < strings.length), i < j →
      (strings[i]!.data.get ⟨col, by {
        rw [h2 0 i (by {exact Nat.zero_lt_of_lt hi}) hi] at hcol
        exact hcol
      }⟩) ≤ (strings[j]!.data.get ⟨col, by {
        rw [h2 0 j (by {exact Nat.zero_lt_of_lt hj}) hj] at hcol
        exact hcol
      }⟩)) :
  min_deletion_size strings = 0 :=
  sorry

theorem min_deletion_size_bounds
  (strings : List String)  
  (h1 : strings.length > 1)
  (h2 : ∀ (i j : Nat), i < strings.length → j < strings.length → 
    strings[i]!.length = strings[j]!.length) :
  ∃ n, min_deletion_size strings = n ∧ 
    0 ≤ n ∧ n ≤ strings[0]!.length :=
  sorry
-- </vc-theorems>