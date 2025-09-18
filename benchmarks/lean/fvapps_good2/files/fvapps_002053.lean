-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_substring_ways (s t : String) : Nat :=
sorry

def is_substring (s t : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_substring_ways_nonnegative (s t : String) :
  0 ≤ count_substring_ways s t ∧ count_substring_ways s t < 1000000007 :=
sorry

theorem substring_gives_nonzero (s t : String)
  (h : t.length > 0)
  (h2 : is_substring s t = true) :
  0 < count_substring_ways s t :=
sorry
-- </vc-theorems>