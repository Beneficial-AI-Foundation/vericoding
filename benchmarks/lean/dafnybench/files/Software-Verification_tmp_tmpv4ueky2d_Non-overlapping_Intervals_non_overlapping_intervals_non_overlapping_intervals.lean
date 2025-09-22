-- <vc-preamble>
def sorted (a : Array (Array Int)) (l : Int) (u : Int) : Prop :=
∀ i j:Nat, 0 ≤ l → l ≤ i → i ≤ j → j ≤ u → u < a.size →
(a[i]!)[1]! ≤ (a[j]!)[1]!

def partitioned (a : Array (Array Int)) (i : Int) : Prop :=
∀ k k':Nat, 0 ≤ k → k ≤ i → i < k' → k' < a.size →
(a[k]!)[1]! ≤ (a[k']!)[1]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bubble_sort (a : Array (Array Int)) : Array (Array Int) :=
sorry

def non_overlapping_intervals (intervals : Array (Array Int)) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bubble_sort_spec (a : Array (Array Int)) :
(a[0]!).size = 2 →
sorted (bubble_sort a) 0 ((bubble_sort a).size - 1) :=
sorry

theorem non_overlapping_intervals_spec (intervals : Array (Array Int)) :
1 ≤ intervals.size →
intervals.size ≤ 100000 →
(∀ i, 0 ≤ i → i < intervals.size → (intervals[i]!).size = 2) →
(∀ i, 0 ≤ i → i < intervals.size → -50000 ≤ (intervals[i]!)[0]! → (intervals[i]!)[0]! ≤ 50000) →
(∀ i, 0 ≤ i → i < intervals.size → -50000 ≤ (intervals[i]!)[1]! → (intervals[i]!)[1]! ≤ 50000) →
non_overlapping_intervals intervals ≥ 0 :=
sorry
-- </vc-theorems>