-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_subsequences (n k : Nat) (s : List Char) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_subsequences_nonnegative (n k : Nat) (s : List Char) :
  count_subsequences n k s ≥ 0 := sorry

theorem no_b_implies_zero (n k : Nat) (s : List Char) :
  (∀ c, c ∈ s → c ≠ 'b') → count_subsequences n k s = 0 := sorry

theorem no_a_implies_zero (n k : Nat) (s : List Char) :
  (∀ c, c ∈ s → c ≠ 'a') → count_subsequences n k s = 0 := sorry

theorem count_monotone_in_k (n k : Nat) (s : List Char) :
  k > 0 → count_subsequences n k s ≥ count_subsequences n (k-1) s := sorry

theorem empty_k_gives_zero (s : List Char) :
  count_subsequences s.length 0 s = 0 := sorry

theorem empty_string_gives_zero (n k : Nat) :
  count_subsequences n k [] = 0 := sorry
-- </vc-theorems>