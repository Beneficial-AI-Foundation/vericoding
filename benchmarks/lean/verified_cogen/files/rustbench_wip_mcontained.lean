-- <vc-preamble>
@[reducible, simp]
def strictSorted (arr : Array Int) : Prop :=
  ∀ k l : Nat, k < l → l < arr.size → arr[k]! < arr[l]!

@[reducible, simp]
def mcontained_precond (v : Array Int) (w : Array Int) (n : Nat) (m : Nat) : Prop :=
  n ≤ m ∧ strictSorted v ∧ strictSorted w ∧ v.size ≥ n ∧ w.size ≥ m
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mcontained (v : Array Int) (w : Array Int) (n : Nat) (m : Nat) (h_precond : mcontained_precond v w n m) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def mcontained_postcond (v : Array Int) (w : Array Int) (n : Nat) (m : Nat) (b : Bool) (h_precond : mcontained_precond v w n m) : Prop :=
  b → (∀ k : Nat, k < n → (∃ j : Nat, j < m ∧ v[k]! = w[j]!))

theorem mcontained_spec_satisfied (v : Array Int) (w : Array Int) (n : Nat) (m : Nat) (h_precond : mcontained_precond v w n m) :
    mcontained_postcond v w n m (mcontained v w n m h_precond) h_precond := by
  sorry
-- </vc-theorems>