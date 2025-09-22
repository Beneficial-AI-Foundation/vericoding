-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MOD := 1000000007

def kConcatenationMaxSum (arr : List Int) (k : Nat) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem kconcat_nonnegative (arr : List Int) (k : Nat) :
  k > 0 → kConcatenationMaxSum arr k ≥ 0 := sorry

theorem kconcat_mod_bound (arr : List Int) (k : Nat) :
  k > 0 → kConcatenationMaxSum arr k < MOD := sorry

theorem kconcat_k1_maxsubarray (arr : List Int) :
  kConcatenationMaxSum arr 1 = kConcatenationMaxSum arr 1 := sorry

theorem kconcat_empty (k : Nat) :
  k > 0 → kConcatenationMaxSum [] k = 0 := sorry

theorem kconcat_monotone_positive (arr : List Int) (k : Nat) :
  k > 1 →
  (arr.foldl (· + ·) 0 > 0) →
  kConcatenationMaxSum arr k ≥ kConcatenationMaxSum arr (k-1) := sorry
-- </vc-theorems>