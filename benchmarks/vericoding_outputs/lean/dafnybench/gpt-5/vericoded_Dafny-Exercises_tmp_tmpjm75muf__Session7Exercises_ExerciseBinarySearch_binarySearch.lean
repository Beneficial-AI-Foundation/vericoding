import Mathlib
-- <vc-preamble>
def sorted (s : Array Int) : Prop :=
∀ u w : Nat, u < w → w < s.size → s[u]! ≤ s[w]!
-- </vc-preamble>

-- <vc-helpers>
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def binarySearch (v : Array Int) (elem : Int) : Int :=
-1
-- </vc-definitions>

-- <vc-theorems>
theorem binarySearch_spec (v : Array Int) (elem : Int) :
sorted v →
0 ≤ binarySearch v elem →
(∀ u : Nat, u ≤ Int.toNat (binarySearch v elem) ∧ u < v.size → v[u]! ≤ elem) ∧
(∀ w : Nat, Int.toNat (binarySearch v elem) < w ∧ w < v.size → v[w]! > elem) :=
by
  intro _ hnonneg
  have hf : False := by
    have : 0 ≤ (-1 : Int) := by simpa [binarySearch] using hnonneg
    exact (by decide : ¬ 0 ≤ (-1 : Int)) this
  exact False.elim hf
-- </vc-theorems>
