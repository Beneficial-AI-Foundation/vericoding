-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_repeating (arr : List Int) : Int × Nat := sorry

def List.sorted (l : List Int) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! ≤ l[j]!
-- </vc-definitions>

-- <vc-theorems>
theorem find_max_repeating_val_exists {arr : List Int} (h : arr ≠ []) : 
  let (val, _) := find_max_repeating arr
  val ∈ arr := sorry

theorem find_max_repeating_count_correct {arr : List Int} (h : arr ≠ []) :
  let (val, count) := find_max_repeating arr  
  (arr.filter (· = val)).length = count := sorry

theorem find_max_repeating_is_max {arr : List Int} (h : arr ≠ []) :
  let (val, count) := find_max_repeating arr
  ∀ x ∈ arr, (arr.filter (· = x)).length ≤ count := sorry

theorem find_max_repeating_smallest {arr : List Int} (h : arr ≠ []) :
  let (val, count) := find_max_repeating arr
  ∀ x ∈ arr, (arr.filter (· = x)).length = count → val ≤ x := sorry

theorem find_max_repeating_count_bounds {arr : List Int} (h : arr ≠ []) :
  let (_, count) := find_max_repeating arr
  1 ≤ count ∧ count ≤ arr.length := sorry

theorem find_max_repeating_sorted {arr : List Int} (h : arr ≠ []) (h2 : arr.sorted) :
  let (val, count) := find_max_repeating arr
  let head := arr.head h
  (arr.filter (· = head)).length = count → val = head := sorry
-- </vc-theorems>