-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def wiggleMaxLength (arr : List Int) : Nat :=
sorry

def isSorted (l : List Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem wiggle_length_bounds (arr : List Int) :
  0 ≤ wiggleMaxLength arr ∧ wiggleMaxLength arr ≤ arr.length :=
sorry

theorem monotonic_increasing_bound (arr : List Int) :
  arr.length > 1 → isSorted arr = true → wiggleMaxLength arr ≤ 2 :=
sorry

theorem small_array_property (arr : List Int) :
  arr.length < 2 → wiggleMaxLength arr = arr.length :=
sorry

theorem monotonic_decreasing_bound (arr : List Int) :
  arr.length > 1 → isSorted (List.reverse arr) = true → wiggleMaxLength arr ≤ 2 :=
sorry

theorem shift_invariance (arr : List Int) (k : Int) :
  wiggleMaxLength arr = wiggleMaxLength (arr.map (· + k)) :=
sorry

theorem scale_invariance (arr : List Int) (k : Int) (h : k ≠ 0) :
  wiggleMaxLength arr = wiggleMaxLength (arr.map (· * k)) :=
sorry

theorem reverse_invariance (arr : List Int) :
  wiggleMaxLength arr = wiggleMaxLength (List.reverse arr) :=
sorry
-- </vc-theorems>