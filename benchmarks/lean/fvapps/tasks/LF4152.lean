-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_unfairness (arr : List Int) (k : Nat) : Int :=
  sorry

def listMax (xs : List Int) : Int :=
  sorry

def listMin (xs : List Int) : Int :=
  sorry

def sortList (xs : List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_unfairness_non_negative {arr : List Int} {k : Nat}
  (h : arr.length > 0) (h2 : k > 0) (h3 : k ≤ arr.length) :
  min_unfairness arr k ≥ 0 :=
sorry

theorem min_unfairness_k_one {arr : List Int}
  (h : arr.length > 0) :
  min_unfairness arr 1 = 0 :=
sorry

theorem min_unfairness_max_difference {arr : List Int} {k : Nat}
  (h1 : arr.length > 1) (h2 : k > 0) (h3 : k ≤ arr.length) :
  min_unfairness arr k ≤ listMax arr - listMin arr :=
sorry

theorem min_unfairness_sort_invariant {arr : List Int} {k : Nat}
  (h1 : k > 1) (h2 : arr.length ≥ k) :
  min_unfairness arr k = min_unfairness (sortList arr) k :=
sorry
-- </vc-theorems>