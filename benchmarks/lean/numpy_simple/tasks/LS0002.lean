-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def arangeLength (start stop step : Float) : Nat :=
sorry

def arange (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    Vector Float (arangeLength start stop step) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem arange_spec
  (start stop step : Float)
  (h_step_nonzero : step ≠ 0)
  (h_valid_range : if step < 0 then start > stop else start < stop) :
  let n := arangeLength start stop step
  let arr := arange start stop step h_step_nonzero h_valid_range
  n = ((stop - start) / step).floor.toUInt64.toNat
  ∧
  n > 0
  ∧
  arr[0]'(by sorry) = start
  ∧
  ∀ i : Fin n, i.val + 1 < n → arr[i.val + 1]'(by sorry) - arr[i.val] = step :=
sorry
-- </vc-theorems>