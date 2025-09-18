-- <vc-preamble>
def pvariance (xs : List String) : Float := sorry

/- Our variance function -/
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def variance (xs : List String) : Float := sorry

/- Our variance matches statistics.pvariance -/
-- </vc-definitions>

-- <vc-theorems>
theorem variance_matches_pvariance (words : List String) (h : words ≠ []) :
  variance words = pvariance words := sorry
-- </vc-theorems>