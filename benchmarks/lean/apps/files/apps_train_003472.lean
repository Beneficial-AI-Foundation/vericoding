def pvariance (xs : List String) : Float := sorry

/- Our variance function -/

-- <vc-helpers>
-- </vc-helpers>

def variance (xs : List String) : Float := sorry

/- Our variance matches statistics.pvariance -/

theorem variance_matches_pvariance (words : List String) (h : words ≠ []) :
  variance words = pvariance words := sorry

/- Words of same length have variance 0 -/

theorem same_length_zero_variance (words : List String) (h1 : words ≠ []) 
  (h2 : ∀ w ∈ words, w.length = 5) : variance words = 0 := sorry

/- Variance is always nonnegative -/

theorem variance_nonnegative (words : List String) (h : words.length ≥ 2) :
  variance words ≥ 0 := sorry

/- Empty list raises error -/

theorem empty_list_error : 
  variance [] = 0/0 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval variance ["Hello", "world"]

/-
info: 2.25
-/
-- #guard_msgs in
-- #eval variance ["Hi", "world"]

/-
info: 7.5556
-/
-- #guard_msgs in
-- #eval variance ["Variance", "is", "not", "a", "good", "stimator"]

-- Apps difficulty: introductory
-- Assurance level: unguarded