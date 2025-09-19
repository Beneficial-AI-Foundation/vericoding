-- <vc-preamble>
def List.maximum (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | (h::t) => t.foldl max h
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_army_strength (n : Nat) (arr : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_at_least_max_element {arr : List Nat} (h : arr ≠ []) : 
  find_max_army_strength arr.length arr ≥ List.maximum arr := by
  sorry

theorem non_negative_result {arr : List Nat} (h : arr ≠ []) :
  find_max_army_strength arr.length arr ≥ 0 := by
  sorry

theorem single_element (x : Nat) :
  find_max_army_strength 1 [x] = x := by
  sorry

theorem two_elements (x y : Nat) :
  find_max_army_strength 2 [x, y] ≥ max x y := by
  sorry

theorem reverse_invariant {arr : List Nat} (h : arr ≠ []) :
  find_max_army_strength arr.length arr = 
  find_max_army_strength arr.length arr.reverse := by
  sorry
-- </vc-theorems>