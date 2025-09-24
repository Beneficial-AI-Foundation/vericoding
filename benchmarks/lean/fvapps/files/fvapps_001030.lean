-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def christmas_box (n : Nat) : List (List Nat) := sorry

theorem christmas_box_empty (n : Nat) : 
  n = 0 → christmas_box n = [] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem christmas_box_length {n : Nat} :
  n > 0 → List.length (christmas_box n) = 2 * n - 1 := sorry

theorem christmas_box_top_bottom_match {n : Nat} :
  n > 1 → 
  List.head! (christmas_box n) = List.getLast! (christmas_box n) := sorry
-- </vc-theorems>