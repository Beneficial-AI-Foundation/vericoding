-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def circularly_sorted (xs : List Int) : Bool :=
  sorry

def isSorted (xs : List Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sorted_is_circular {xs : List Int} (h : xs.length > 0) :
  isSorted xs → circularly_sorted xs = true :=
sorry

theorem rotated_sorted_is_circular {xs : List Int} (h : xs.length > 0) (distinct : List.Nodup xs) :
  ∀ i, i < xs.length → circularly_sorted (List.drop i xs ++ List.take i xs) = true :=
sorry

theorem singleton_is_circular {x : Int} :
  circularly_sorted [x] = true :=
sorry

theorem empty_raises {xs : List Int} (h : xs.length = 0) :
  circularly_sorted xs = false :=
sorry

theorem unsorted_not_circular {xs : List Int} (h : xs.length > 1)
  (not_sorted : ∀ i, i < xs.length → ¬(isSorted (List.drop i xs ++ List.take i xs))) :
  circularly_sorted xs = false :=
sorry
-- </vc-theorems>