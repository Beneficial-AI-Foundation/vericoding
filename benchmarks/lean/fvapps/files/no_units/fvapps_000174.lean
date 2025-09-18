-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_window (s t : String) : String := sorry

def verify_contains (window target : String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_window_empty_target {s : String} : 
  min_window s "" = "" := sorry

theorem min_window_is_substring {s t : String} (h : min_window s t ≠ "") :
  ∃ (i j : Nat), i ≤ j ∧ j ≤ s.length ∧
  min_window s t = s.extract (String.Pos.mk i) (String.Pos.mk j) := sorry

theorem min_window_contains_target {s t : String} (h : min_window s t ≠ "") :
  verify_contains (min_window s t) t = true := sorry

theorem min_window_is_minimal {s t : String} (h : min_window s t ≠ "") :
  ∀ (i j : Nat), i < j → j ≤ (min_window s t).length →
    verify_contains ((min_window s t).extract (String.Pos.mk i) (String.Pos.mk j)) t = false := sorry

theorem min_window_single_char {s t : String} (h1 : t.length = 1) :
  (∃ (i : Nat), i < s.length ∧ s.get (String.Pos.mk i) = t.get (String.Pos.mk 0)) →
  (min_window s t).length = 1 ∧ min_window s t = t := sorry

theorem min_window_length_bounds {s t : String} :
  (min_window s t).length ≤ s.length ∧ 
  (min_window s t ≠ "" → (min_window s t).length ≥ t.data.eraseDups.length) := sorry
-- </vc-theorems>