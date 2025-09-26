-- <vc-preamble>
def List.sum [Add α] : List α → α 
  | [] => sorry
  | (x::xs) => x + List.sum xs

def redistributeWealth (l : List Int) : List Int :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def redistributeWealthFloat (l : List Float) : List Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem redistributeWealth_preserves_length (l : List Int) :
  (redistributeWealth l).length = l.length := by sorry

theorem redistributeWealth_all_equal (l : List Int) (h : l.length > 0) :
  ∀ x ∈ redistributeWealth l, x = (redistributeWealth l).head! := by sorry

theorem redistributeWealth_preserves_sum (l : List Int) :
  (redistributeWealth l).sum = l.sum := by sorry

theorem redistributeWealth_gives_mean (l : List Int) (h : l.length > 0) :
  ∀ x ∈ redistributeWealth l, x = l.sum / l.length := by sorry

theorem redistributeWealthFloat_preserves_length (l : List Float) :
  (redistributeWealthFloat l).length = l.length := by sorry

theorem redistributeWealthFloat_all_equal (l : List Float) (h : l.length > 0) :
  ∀ x ∈ redistributeWealthFloat l, x = (redistributeWealthFloat l).head! := by sorry

theorem redistributeWealthFloat_preserves_sum (l : List Float) :
  (redistributeWealthFloat l).sum = l.sum := by sorry
-- </vc-theorems>