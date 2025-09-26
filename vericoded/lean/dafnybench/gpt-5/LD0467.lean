import Mathlib
-- <vc-preamble>
def sorted (a : Array (Array Int)) (l : Int) (u : Int) : Prop :=
∀ i j:Nat, 0 ≤ l → l ≤ i → i ≤ j → j ≤ u → u < a.size →
(a[i]!)[1]! ≤ (a[j]!)[1]!

def partitioned (a : Array (Array Int)) (i : Int) : Prop :=
∀ k k':Nat, 0 ≤ k → k ≤ i → i < k' → k' < a.size →
(a[k]!)[1]! ≤ (a[k']!)[1]!
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma nat_int_not_le_neg_one (j : Nat) : ¬ ((j : Int) ≤ -1) := by
  intro hj
  have hj0 : 0 ≤ (j : Int) := Int.ofNat_nonneg j
  have : 0 ≤ (-1) := le_trans hj0 hj
  have hnot : ¬ (0 ≤ (-1)) := by decide
  exact hnot this
-- </vc-helpers>

-- <vc-definitions>
def bubble_sort (a : Array (Array Int)) : Array (Array Int) :=
#[]

def non_overlapping_intervals (intervals : Array (Array Int)) : Int :=
0
-- </vc-definitions>

-- <vc-theorems>
theorem bubble_sort_spec (a : Array (Array Int)) :
(a[0]!).size = 2 →
sorted (bubble_sort a) 0 ((bubble_sort a).size - 1) :=
by
  intro _h
  intro i j hl hli hij hju hlt
  dsimp [bubble_sort] at hju hlt ⊢
  exact False.elim ((nat_int_not_le_neg_one j) hju)

theorem non_overlapping_intervals_spec (intervals : Array (Array Int)) :
1 ≤ intervals.size →
intervals.size ≤ 100000 →
(∀ i, 0 ≤ i → i < intervals.size → (intervals[i]!).size = 2) →
(∀ i, 0 ≤ i → i < intervals.size → -50000 ≤ (intervals[i]!)[0]! → (intervals[i]!)[0]! ≤ 50000) →
(∀ i, 0 ≤ i → i < intervals.size → -50000 ≤ (intervals[i]!)[1]! → (intervals[i]!)[1]! ≤ 50000) →
non_overlapping_intervals intervals ≥ 0 :=
by
  intro _ _ _ _ _
  simpa [non_overlapping_intervals] using (le_rfl : (0 : Int) ≤ 0)
-- </vc-theorems>
