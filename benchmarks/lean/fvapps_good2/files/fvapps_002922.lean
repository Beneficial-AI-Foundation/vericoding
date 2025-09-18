-- <vc-preamble>
def isSorted (l : List Int) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! ≤ l[j]!

def swap (l : List Int) (i j : Nat) (h1 : i < l.length) (h2 : j < l.length) : List Int :=
  let arr := l.toArray
  let tmp := arr[i]!
  let arr := arr.set! i arr[j]!
  let arr := arr.set! j tmp
  arr.toList
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_inversions (lst : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_list_zero_inversions :
  count_inversions [] = 0 := by
  sorry

theorem sorted_list_zero_inversions {lst : List Int} :
  isSorted lst → count_inversions lst = 0 := by
  sorry

theorem reversed_sorted_unique_inversions {lst : List Int} (h1 : List.Nodup lst) (h2 : isSorted lst) :
  count_inversions (List.reverse lst) = (lst.length * (lst.length - 1)) / 2 := by
  sorry

theorem single_swap_one_inversion {lst : List Int} (h1 : isSorted lst) (h2 : lst.length ≥ 2)
  (h3 : lst[0]! ≠ lst[1]!)
  (h4 : 0 < lst.length) (h5 : 1 < lst.length) :
  count_inversions (swap lst 0 1 h4 h5) = 1 := by
  sorry

theorem count_always_non_negative (lst : List Int) :
  count_inversions lst ≥ 0 := by
  sorry
-- </vc-theorems>