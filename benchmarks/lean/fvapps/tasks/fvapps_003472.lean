-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pvariance (xs : List String) : Float :=
sorry

def variance (xs : List String) : Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem variance_matches_pvariance (words : List String) (h : words ≠ []) :
  variance words = pvariance words :=
sorry

theorem same_length_zero_variance (words : List String) (h1 : words ≠ [])
  (h2 : ∀ w ∈ words, w.length = 5) : variance words = 0 :=
sorry

theorem variance_nonnegative (words : List String) (h : words.length ≥ 2) :
  variance words ≥ 0 :=
sorry

theorem empty_list_error :
  variance [] = 0/0 :=
sorry
-- </vc-theorems>