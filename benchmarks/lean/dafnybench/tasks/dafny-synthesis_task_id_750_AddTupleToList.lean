-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def AddTupleToList (l : Array (Int × Int)) (t : Int × Int) : Array (Int × Int) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem AddTupleToList_spec (l : Array (Int × Int)) (t : Int × Int) :
let r := AddTupleToList l t
r.size = l.size + 1 ∧
r[r.size - 1]! = t ∧
∀ i, 0 ≤ i ∧ i < l.size → r[i]! = l[i]! :=
sorry
-- </vc-theorems>