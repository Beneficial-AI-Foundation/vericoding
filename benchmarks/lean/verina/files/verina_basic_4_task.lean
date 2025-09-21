-- <vc-preamble>
@[reducible, simp]
def kthElement_precond (arr : Array Int) (k : Nat) : Prop :=
  k ≥ 1 ∧ k ≤ arr.size
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def kthElement (arr : Array Int) (k : Nat) (h_precond : kthElement_precond (arr) (k)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def kthElement_postcond (arr : Array Int) (k : Nat) (result: Int) (h_precond : kthElement_precond (arr) (k)) :=
  arr.any (fun x => x = result ∧ x = arr[k - 1]!)

theorem kthElement_spec_satisfied (arr: Array Int) (k: Nat) (h_precond : kthElement_precond (arr) (k)) :
    kthElement_postcond (arr) (k) (kthElement (arr) (k) h_precond) h_precond := by
  sorry
-- </vc-theorems>