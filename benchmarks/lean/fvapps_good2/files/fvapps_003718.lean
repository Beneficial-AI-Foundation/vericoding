-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mean_vs_median (l : List Int) : String :=
sorry

def statistical_mean (l : List Int) : Float :=
sorry

def statistical_median (l : List Int) : Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mean_vs_median_matches_statistics (l : List Int) (h : l ≠ []) :
  let mean := statistical_mean l
  let median := statistical_median l
  mean_vs_median l = (if mean > median then "mean"
                     else if median > mean then "median"
                     else "same") :=
sorry

theorem identical_numbers_return_same (l : List Int) (h1 : l ≠ [])
  (h2 : ∀ x ∈ l, x = 1) :
  mean_vs_median l = "same" :=
sorry
-- </vc-theorems>