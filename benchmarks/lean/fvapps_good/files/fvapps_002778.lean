-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nbMonths (oldCarPrice : Int) (newCarPrice : Int) (saving : Int) (loss : Float) : Int × Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nb_months_non_negative (oldCarPrice newCarPrice saving : Int) (loss : Float)
  (h1 : oldCarPrice > 0) (h2 : newCarPrice > 0) (h3 : saving > 0) (h4 : loss > 0) :
  let (months, _) := nbMonths oldCarPrice newCarPrice saving loss
  months ≥ 0 := sorry

theorem nb_months_zero_when_old_more_expensive (oldCarPrice newCarPrice saving : Int) (loss : Float)
  (h1 : oldCarPrice ≥ newCarPrice) (h2 : oldCarPrice > 0) (h3 : newCarPrice > 0) 
  (h4 : saving > 0) (h5 : loss > 0) :
  let (months, _) := nbMonths oldCarPrice newCarPrice saving loss
  months = 0 := sorry

theorem nb_months_budget_sufficient (oldCarPrice newCarPrice saving : Int) (loss : Float)
  (h1 : oldCarPrice > 0) (h2 : newCarPrice > 0) (h3 : saving > 0) (h4 : loss > 0) :
  let (months, _) := nbMonths oldCarPrice newCarPrice saving loss
  let final_old_price := Float.ofInt oldCarPrice * ((100 - loss - Float.ofInt months/2 * 0.5)/100)
  let final_new_price := Float.ofInt newCarPrice * ((100 - loss - Float.ofInt months/2 * 0.5)/100)
  final_old_price + Float.ofInt (saving * months) ≥ final_new_price := sorry

theorem nb_months_same_price_zero (price saving : Int) (loss : Float)
  (h1 : price > 0) (h2 : saving > 0) (h3 : loss > 0) :
  nbMonths price price saving loss = (0, 0) := sorry
-- </vc-theorems>