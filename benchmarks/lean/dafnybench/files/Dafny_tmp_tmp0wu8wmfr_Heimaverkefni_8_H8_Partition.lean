-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Partition (m : Array Int) :
m.size > 0 → (Array Int × Int × Array Int) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Partition_spec (m : Array Int) (h : m.size > 0) :
let (pre, p, post) := Partition m h

-- Ensures p is in original array

(∃ i : Nat, i < m.size ∧ m[i]! = p) ∧

-- Ensures all elements from original array appear in the result

(∀ x : Int, (∃ i : Nat, i < m.size ∧ m[i]! = x) →

(∃ j : Nat, j < pre.size ∧ pre[j]! = x) ∨

x = p ∨

(∃ k : Nat, k < post.size ∧ post[k]! = x)) ∧

-- Ensures pre elements are ≤ p

(∀ i : Nat, i < pre.size → pre[i]! ≤ p) ∧

-- Ensures post elements are ≥ p

(∀ i : Nat, i < post.size → post[i]! ≥ p) :=
sorry
-- </vc-theorems>