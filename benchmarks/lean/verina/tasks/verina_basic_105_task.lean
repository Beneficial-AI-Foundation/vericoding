-- <vc-preamble>
@[reducible, simp]
def arrayProduct_precond (a : Array Int) (b : Array Int) : Prop :=
  a.size = b.size
-- </vc-preamble>

-- <vc-helpers>
def loop (a b : Array Int) (len : Nat) : Nat → Array Int → Array Int
  | i, c =>
    if i < len then
      let a_val := if i < a.size then a[i]! else 0
      let b_val := if i < b.size then b[i]! else 0
      let new_c := Array.set! c i (a_val * b_val)
      loop a b len (i+1) new_c
    else c
-- </vc-helpers>

-- <vc-definitions>
def arrayProduct (a : Array Int) (b : Array Int) (h_precond : arrayProduct_precond (a) (b)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def arrayProduct_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : arrayProduct_precond (a) (b)) :=
  (result.size = a.size) ∧ (∀ i, i < a.size → a[i]! * b[i]! = result[i]!)

theorem arrayProduct_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : arrayProduct_precond (a) (b)) :
    arrayProduct_postcond (a) (b) (arrayProduct (a) (b) h_precond) h_precond := by
  sorry
-- </vc-theorems>