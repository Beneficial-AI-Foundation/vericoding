-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_ambiguous_pairs (m d w : Nat) : Nat := sorry

theorem count_ambiguous_pairs_nonnegative (m d w : Nat) 
    (h1: m ≥ 1) (h2: d ≥ 1) (h3: w ≥ 1) :
    count_ambiguous_pairs m d w ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_ambiguous_pairs_equal_inputs (n : Nat) (h: n ≥ 1) :
    count_ambiguous_pairs n n n ≤ n * (n-1) / 2 := sorry

theorem count_ambiguous_pairs_week_one (m d : Nat) (h1: m ≥ 1) (h2: d ≥ 1) :
    count_ambiguous_pairs m d 1 ≤ min m d * (min m d - 1) / 2 := sorry
-- </vc-theorems>