-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def prod_partitions (n : Nat) : String := sorry
def factorial (n : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem prod_partitions_output_format (n : Nat) : 
  n ≥ 1 → 
  let result := prod_partitions n 
  let parts := (result.splitOn " ")
  parts.length = 6 ∧ 
  parts[0]! = "Range:" ∧
  parts[2]! = "Average:" ∧
  parts[4]! = "Median:" ∧
  (String.toNat? parts[1]!).isSome
  := sorry

theorem prod_partitions_properties (n : Nat) :
  n ≥ 1 →
  let result := prod_partitions n
  let parts := (result.splitOn " ")
  match String.toNat? parts[1]! with
  | some range_val => 
    range_val ≤ factorial n ∧
    range_val ≥ 0
  | none => False
  := sorry
-- </vc-theorems>