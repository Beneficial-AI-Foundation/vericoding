-- <vc-preamble>
def isSortedList (l : List Int) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! ≤ l[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_intersection (arr1 arr2 : List Int) : List Int := sorry

def sortList (l : List Int) : List Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem self_intersection {arr : List Int} :
  get_intersection arr arr = sortList arr :=
sorry

theorem intersection_sorted {arr1 arr2 : List Int} :
  isSortedList (get_intersection arr1 arr2) :=
sorry

theorem intersection_elements_in_both {arr1 arr2 : List Int} (x : Int) :
  x ∈ get_intersection arr1 arr2 → x ∈ arr1 ∧ x ∈ arr2 :=
sorry

theorem intersection_count_bound {arr1 arr2 : List Int} (x : Int) :
  (get_intersection arr1 arr2).count x ≤ min (arr1.count x) (arr2.count x) :=
sorry

theorem empty_intersection_left {arr : List Int} :
  get_intersection [] arr = [] :=
sorry

theorem empty_intersection_right {arr : List Int} :
  get_intersection arr [] = [] :=
sorry

theorem intersection_commutative {arr1 arr2 : List Int} :
  get_intersection arr1 arr2 = get_intersection arr2 arr1 :=
sorry
-- </vc-theorems>