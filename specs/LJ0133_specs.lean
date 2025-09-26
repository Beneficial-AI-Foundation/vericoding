-- <vc-preamble>
-- Spec function f translated from Verus
def f (seq : List Nat) (i : Int) : Prop :=
  seq[i.natAbs]! = i + 2

@[reducible, simp]
def getElementCheckProperty_precond (arr : Array Nat) (i : Nat) : Prop :=
  arr.size > 0 ∧ 0 < i ∧ i < arr.size ∧ (∀ i : Int, f arr.toList i)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getElementCheckProperty (arr : Array Nat) (i : Nat) (h_precond : getElementCheckProperty_precond arr i) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def getElementCheckProperty_postcond (arr : Array Nat) (i : Nat) (ret : Nat) (h_precond : getElementCheckProperty_precond arr i) : Prop :=
  ret = i + 2 ∧ ret = arr[i]!

theorem getElementCheckProperty_spec_satisfied (arr : Array Nat) (i : Nat) (h_precond : getElementCheckProperty_precond arr i) :
    getElementCheckProperty_postcond arr i (getElementCheckProperty arr i h_precond) h_precond := by
  sorry
-- </vc-theorems>