-- <vc-preamble>
def isSorted (l : List Int) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! < l[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_number_of_lis (nums : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem number_of_lis_properties (nums : List Int) :
  let result := find_number_of_lis nums
  result ≥ 0 ∧
  (nums = [] → result = 0)
:= by
sorry

theorem constant_list_property {n : Nat} (x : Int) :
  find_number_of_lis (List.replicate n x) = n
:= by
sorry

theorem strictly_increasing_property (nums : List Int) (h : nums ≠ []) :
  isSorted nums →
  find_number_of_lis nums = 1
:= by
sorry
-- </vc-theorems>