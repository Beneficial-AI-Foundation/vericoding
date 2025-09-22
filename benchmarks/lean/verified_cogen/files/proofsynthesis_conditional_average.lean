-- <vc-preamble>
@[reducible, simp]
def conditionalAverage_precond (vals_1 : Array UInt64) (vals_2 : Array UInt64) (conds_1 : Array Bool) (conds_2 : Array Bool) (avgs : Array UInt64) :=
  vals_1.size = vals_2.size ∧
  vals_1.size = conds_1.size ∧
  vals_1.size = conds_2.size ∧
  (∀ idx : Nat, idx < vals_1.size → conds_1[idx]! ∨ conds_2[idx]!) ∧
  (∀ idx : Nat, idx < vals_1.size → vals_1[idx]! < 1000) ∧
  (∀ idx : Nat, idx < vals_2.size → vals_2[idx]! < 1000)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def conditionalAverage (vals_1 : Array UInt64) (vals_2 : Array UInt64) (conds_1 : Array Bool) (conds_2 : Array Bool) (avgs : Array UInt64) (h_precond : conditionalAverage_precond vals_1 vals_2 conds_1 conds_2 avgs) : Array UInt64 :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def conditionalAverage_postcond (vals_1 : Array UInt64) (vals_2 : Array UInt64) (conds_1 : Array Bool) (conds_2 : Array Bool) (avgs : Array UInt64) (result : Array UInt64) (h_precond : conditionalAverage_precond vals_1 vals_2 conds_1 conds_2 avgs) :=
  result.size = vals_1.size ∧
  (∀ idx : Nat, idx < vals_1.size →
    ((conds_1[idx]! ∧ conds_2[idx]!) → result[idx]! = (vals_1[idx]! + vals_2[idx]!) / 2) ∧
    ((conds_1[idx]! ∧ ¬conds_2[idx]!) → result[idx]! = vals_1[idx]!) ∧
    ((¬conds_1[idx]! ∧ conds_2[idx]!) → result[idx]! = vals_2[idx]!))

theorem conditionalAverage_spec_satisfied (vals_1 : Array UInt64) (vals_2 : Array UInt64) (conds_1 : Array Bool) (conds_2 : Array Bool) (avgs : Array UInt64) (h_precond : conditionalAverage_precond vals_1 vals_2 conds_1 conds_2 avgs) :
    conditionalAverage_postcond vals_1 vals_2 conds_1 conds_2 avgs (conditionalAverage vals_1 vals_2 conds_1 conds_2 avgs h_precond) h_precond := by
  sorry
-- </vc-theorems>