/-
Let us begin with an example:

A man has a rather old car being worth $2000. 
He saw a secondhand car being worth $8000. He wants to keep his old car until he can buy the secondhand one.

He thinks he can save $1000 each month but the prices of his old 
car and of the new one decrease of 1.5 percent per month.
Furthermore this percent of loss increases of `0.5` percent 
at the end of every two months.
Our man finds it difficult to make all these calculations.

**Can you help him?**

How many months will it take him to save up enough money to buy the car he wants, and how much money will he have left over?

**Parameters and return of function:**
```
parameter (positive int or float, guaranteed) startPriceOld (Old car price)
parameter (positive int or float, guaranteed) startPriceNew (New car price)
parameter (positive int or float, guaranteed) savingperMonth 
parameter (positive float or int, guaranteed) percentLossByMonth

nbMonths(2000, 8000, 1000, 1.5) should return [6, 766] or (6, 766)
```
###  Detail of the above example:
```
end month 1: percentLoss 1.5 available -4910.0
end month 2: percentLoss 2.0 available -3791.7999...
end month 3: percentLoss 2.0 available -2675.964
end month 4: percentLoss 2.5 available -1534.06489...
end month 5: percentLoss 2.5 available -395.71327...
end month 6: percentLoss 3.0 available 766.158120825...
return [6, 766] or (6, 766)

```

where `6` is the number of months at **the end of which** he can buy the new car and `766` is the nearest integer to `766.158...` (rounding `766.158` gives `766`).

**Note:** 

Selling, buying and saving are normally done at end of month.
Calculations are processed at the end of each considered month
but if, by chance from the start, the value of the old car is bigger than the value of the new one or equal there is no saving to be made, no need to wait so he can at the beginning of the month buy the new car:
```
nbMonths(12000, 8000, 1000, 1.5) should return [0, 4000]
nbMonths(8000, 8000, 1000, 1.5) should return [0, 0]
```

We don't take care of a deposit of savings in a bank:-)
-/

-- <vc-helpers>
-- </vc-helpers>

def nbMonths (oldCarPrice : Int) (newCarPrice : Int) (saving : Int) (loss : Float) : Int × Float :=
  sorry

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

-- Apps difficulty: introductory
-- Assurance level: guarded