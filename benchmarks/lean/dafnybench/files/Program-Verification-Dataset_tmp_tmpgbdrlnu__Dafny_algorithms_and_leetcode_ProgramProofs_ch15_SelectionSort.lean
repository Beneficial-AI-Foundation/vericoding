-- <vc-preamble>
def count (a : Array Int) (x : Int) : Nat :=
a.foldl (fun acc y => if y = x then acc + 1 else acc) 0

def SplitPoint (a : Array Int) (n : Nat) : Prop :=
∀ i j, 0 ≤ i ∧ i < n ∧ n ≤ j ∧ j < a.size → a[i]! ≤ a[j]!

def SwapFrame (a a' : Array Int) (lo hi : Nat) : Prop :=
(∀ i, (0 ≤ i ∧ i < lo) ∨ (hi ≤ i ∧ i < a.size) → a[i]! = a'[i]!) ∧
(∀ x : Int, count a x = count a' x)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SelectionSort (a : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem SelectionSort_spec (a : Array Int) :
let result := SelectionSort a
(∀ i j, 0 ≤ i ∧ i < j ∧ j < result.size → result[i]! ≤ result[j]!) ∧
result.size = a.size :=
sorry
-- </vc-theorems>