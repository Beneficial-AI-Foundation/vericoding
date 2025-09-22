-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sort_array (arr : List Int) : List Int := sorry

def isSorted (l : List Int) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! ≤ l[j]!
-- </vc-definitions>

-- <vc-theorems>
theorem sort_array_preserves_evens (arr : List Int) : 
  let result := sort_array arr
  List.length arr = List.length result ∧
  ∀ i, i < arr.length → 
    (arr[i]! % 2 = 0 → result[i]! = arr[i]!) := sorry

theorem sort_array_sorts_odds (arr : List Int) :
  let result := sort_array arr
  let odds := result.filter (fun x => x % 2 ≠ 0)
  isSorted odds := sorry

theorem sort_array_preserves_odd_count (arr : List Int) :
  let result := sort_array arr
  (arr.filter (fun x => x % 2 ≠ 0)).length = 
  (result.filter (fun x => x % 2 ≠ 0)).length := sorry
-- </vc-theorems>