-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (arr : List Nat) : Option (List Nat) := sorry

theorem solve_preserves_length {arr : List Nat} {result : List Nat} :
  solve arr = some result → result.length = arr.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_preserves_elements {arr : List Nat} {result : List Nat} :
  solve arr = some result → 
  ∀ x, x ∈ arr ↔ x ∈ result := sorry

theorem solve_adjacent_pairs_rule {arr : List Nat} {result : List Nat} :
  solve arr = some result →
  ∀ i, i < result.length - 1 → 
    (result[i]! * 2 = result[i+1]! ∨ result[i]! = result[i+1]! * 3) := sorry

theorem solve_duplicates {arr : List Nat} :
  ¬arr.Nodup → solve arr = none := sorry 

theorem solve_empty :
  solve [] = none := sorry

theorem solve_single (n : Nat) :
  solve [n] = some [n] := sorry
-- </vc-theorems>