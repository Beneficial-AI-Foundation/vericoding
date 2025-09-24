-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def piecewise {n m : Nat} (x : Vector Float n) (condlist : Vector (Float → Bool) m) (funclist : Vector (Float → Float) m) : Vector Float n :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem piecewise_spec {n m : Nat} (x : Vector Float n) (condlist : Vector (Float → Bool) m) (funclist : Vector (Float → Float) m)
  (h : m = m) :
  let ret := piecewise x condlist funclist
  (ret.toList.length = n) ∧
  (∀ i j : Nat, i < n → j < m →
    condlist[j]! (x[i]!) → ret[i]! = funclist[j]! (x[i]!)) :=
sorry
-- </vc-theorems>