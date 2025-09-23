-- <vc-preamble>
def getSize (i j : Int) : Int :=
j - i + 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longestZero (a : Array Int) : Int × Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem longestZero_spec (a : Array Int) :
1 ≤ a.size →
let (sz, pos) := longestZero a
0 ≤ sz ∧ sz ≤ a.size ∧
0 ≤ pos ∧ pos < a.size ∧
pos + sz ≤ a.size ∧
(∀ i:Nat, pos ≤ i ∧ i < pos + sz → a[i]! = 0) ∧
(∀ i j:Nat, 0 ≤ i ∧ i < j ∧ j < a.size ∧ getSize i j > sz →
∃ k, i ≤ k ∧ k ≤ j ∧ a[k]! ≠ 0) :=
sorry
-- </vc-theorems>