-- <vc-preamble>
@[reducible, simp]
def binarySearchRecursive_precond (v : Array Int) (elem : Int) (c : Nat) (f : Nat) :=
  v.size ≤ 100000 ∧ 
  (∀ i j, i < j ∧ j < v.size → v[i]! ≤ v[j]!) ∧
  c ≤ f + 1 ∧ f + 1 ≤ v.size ∧
  (∀ k, k < c → v[k]! ≤ elem) ∧
  (∀ k, f < k ∧ k < v.size → v[k]! > elem)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def binarySearchRecursive (v : Array Int) (elem : Int) (c : Nat) (f : Nat) (h_precond : binarySearchRecursive_precond v elem c f) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def binarySearchRecursive_postcond (v : Array Int) (elem : Int) (c : Nat) (f : Nat) (p : Int) (_ : binarySearchRecursive_precond v elem c f) :=
  -1 ≤ p ∧ p < v.size ∧
  (∀ u, u ≤ p → v[u.natAbs]! ≤ elem) ∧
  (∀ w, p < w ∧ w < v.size → v[w.natAbs]! > elem)

theorem binarySearchRecursive_spec_satisfied (v : Array Int) (elem : Int) (c : Nat) (f : Nat) (h_precond : binarySearchRecursive_precond v elem c f) :
    binarySearchRecursive_postcond v elem c f (binarySearchRecursive v elem c f h_precond) h_precond := by
  sorry
-- </vc-theorems>