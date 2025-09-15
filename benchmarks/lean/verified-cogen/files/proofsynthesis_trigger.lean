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

/- Example usage and test cases would go here -/