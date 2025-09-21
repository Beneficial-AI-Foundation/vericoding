-- <vc-preamble>
@[reducible, simp]
def LinearSearch_precond (a : Array Int) (e : Int) : Prop :=
  ∃ i, i < a.size ∧ a[i]! = e
-- </vc-preamble>

-- <vc-helpers>
def linearSearchAux (a : Array Int) (e : Int) (n : Nat) : Nat :=
  if n < a.size then
    if a[n]! = e then n else linearSearchAux a e (n + 1)
  else
    0
-- </vc-helpers>

-- <vc-definitions>
def LinearSearch (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def LinearSearch_postcond (a : Array Int) (e : Int) (result: Nat) (h_precond : LinearSearch_precond (a) (e)) :=
  (result < a.size) ∧ (a[result]! = e) ∧ (∀ k : Nat, k < result → a[k]! ≠ e)

theorem LinearSearch_spec_satisfied (a: Array Int) (e: Int) (h_precond : LinearSearch_precond (a) (e)) :
    LinearSearch_postcond (a) (e) (LinearSearch (a) (e) h_precond) h_precond := by
  sorry
-- </vc-theorems>