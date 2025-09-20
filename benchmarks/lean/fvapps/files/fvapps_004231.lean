-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def feast (beast dish : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem feast_properties (beast dish : String) 
  (h1 : beast.length > 0) (h2 : dish.length > 0) :
  feast beast dish = (beast.front == dish.front ∧ beast.back == dish.back) :=
sorry

theorem feast_same_string (s : String) (h : s.length > 0) :
  feast s s = true :=
sorry

theorem feast_first_last_only (beast dish : String)
  (h1 : beast.length > 1) (h2 : dish.length > 1) :
  let modifiedDish := String.mk [beast.front] ++ String.mk [beast.back]
  feast beast modifiedDish = true :=
sorry
-- </vc-theorems>