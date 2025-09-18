-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def checkIfCanBreak (s1 s2 : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_if_can_break_same_length (s1 s2 : String) :
  checkIfCanBreak s1 s2 → String.length s1 = String.length s2 :=
sorry

theorem check_if_can_break_reflexive (s : String) :
  checkIfCanBreak s s = true :=
sorry

theorem check_if_can_break_symmetric (s1 s2 : String) :
  checkIfCanBreak s1 s2 = checkIfCanBreak s2 s1 :=
sorry

theorem sorted_string_breaks_unsorted (s sorted : String)
  (h : ∀ i j : String.Pos, i < j → sorted.get i ≤ sorted.get j)
  (h2 : sorted.length = s.length)
  (h3 : ∀ c, c ∈ sorted.data ↔ c ∈ s.data) :
  checkIfCanBreak sorted s = true :=
sorry
-- </vc-theorems>