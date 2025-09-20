-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hamming_distance (a b : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hamming_distance_nonnegative (a b : String) :
  hamming_distance a b ≥ 0 := 
  sorry

theorem hamming_distance_bounded (a b : String) :
  hamming_distance a b ≤ a.length :=
  sorry

theorem hamming_distance_symmetric (a b : String) :
  hamming_distance a b = hamming_distance b a :=
  sorry

theorem hamming_distance_identity (a : String) :
  hamming_distance a a = 0 :=
  sorry

theorem hamming_distance_counts_differences (a b : String) (h : a.length = b.length) :
  hamming_distance a b = ((String.toList a).zip (String.toList b)).countP (fun (x, y) => x ≠ y) :=
  sorry
-- </vc-theorems>