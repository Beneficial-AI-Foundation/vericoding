-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def penultimate {α : Type} (xs : List α) : Option α := sorry

theorem penultimate_list_eq_secondlast {α : Type} (xs : List α) (h : xs.length ≥ 2) :
  penultimate xs = xs.get? (xs.length - 2) := 
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem penultimate_string_eq_secondlast (s : String) (h : s.length ≥ 2) :
  penultimate (s.toList) = (s.toList).get? (s.length - 2) := 
sorry

theorem penultimate_empty_is_none {α : Type} (xs : List α) (h : xs.length < 2) :
  penultimate xs = none :=
sorry

theorem penultimate_singleton_is_none {α : Type} (x : α) :
  penultimate [x] = none :=
sorry
-- </vc-theorems>