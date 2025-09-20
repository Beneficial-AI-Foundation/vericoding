-- <vc-preamble>
def List.maximum : List Int → Option Int 
  | [] => none
  | (h::t) => some (t.foldl max h)

def List.minimum : List Int → Option Int
  | [] => none
  | (h::t) => some (t.foldl min h)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def between_extremes (nums : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem between_extremes_nonnegative (nums : List Int) (h : nums ≠ []) :
  between_extremes nums ≥ 0 := 
  sorry

theorem between_extremes_singleton (n : Int) :
  between_extremes [n] = 0 :=
  sorry
-- </vc-theorems>