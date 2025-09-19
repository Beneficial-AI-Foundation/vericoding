-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_sorted_and_how (arr : List Int) : String :=
sorry

def isSorted (arr : List Int) : Bool :=
sorry

def isSortedDesc (arr : List Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sorted_properties (arr : List Int) (h : arr.length > 0) :
  match is_sorted_and_how arr with
  | "yes, ascending" => isSorted arr = true
  | "yes, descending" => isSortedDesc arr = true
  | _ => ¬(isSorted arr) ∧ ¬(isSortedDesc arr)
  :=
sorry

theorem result_is_valid (arr : List Int) (h : arr.length > 0) :
  is_sorted_and_how arr = "yes, ascending" ∨
  is_sorted_and_how arr = "yes, descending" ∨
  is_sorted_and_how arr = "no"
  :=
sorry

theorem ascending_lists (arr : List Int) (h : arr.length > 0) (h2 : isSorted arr) :
  is_sorted_and_how arr = "yes, ascending"
  :=
sorry
-- </vc-theorems>