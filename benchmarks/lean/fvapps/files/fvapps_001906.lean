-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_longest_chain (pairs : List (Int × Int)) : Nat := sorry

theorem chain_length_bounds (pairs : List (Int × Int)) :
  pairs ≠ [] →
  1 ≤ find_longest_chain pairs ∧ find_longest_chain pairs ≤ pairs.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem chain_length_invariant_under_list_ordering (pairs₁ pairs₂ : List (Int × Int)) :
  pairs₁.length = pairs₂.length → 
  find_longest_chain pairs₁ = find_longest_chain pairs₂ := sorry

theorem overlapping_pairs_property (pairs : List (Int × Int)) (first : Int × Int) :
  pairs ≠ [] →
  let overlapping := [(first.1, first.2 + 1)]
  find_longest_chain (pairs ++ overlapping) ≤ find_longest_chain pairs + 1 := sorry

theorem non_overlapping_sequence_length (n : Nat) :
  let pairs := List.map (fun i => (Int.ofNat (2 * i), Int.ofNat (2 * i + 1))) (List.range n)
  find_longest_chain pairs = n := sorry
-- </vc-theorems>