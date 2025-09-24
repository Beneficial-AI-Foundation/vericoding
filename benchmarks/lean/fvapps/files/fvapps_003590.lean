-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_three_and_two (list : List α) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem list_length_is_five {α : Type} (list : List α) :
  check_three_and_two list = true → list.length = 5 :=
  sorry

theorem counts_must_be_two_and_three {α : Type} [BEq α] (list : List α) :
  check_three_and_two list = true →
  ∃ (x y : α), 
    (list.count x = 2 ∧ list.count y = 3) ∨ 
    (list.count x = 3 ∧ list.count y = 2) :=
  sorry

theorem counts_two_and_three_implies_true {α : Type} [BEq α] (list : List α) :
  (∃ (x y : α), 
    (list.count x = 2 ∧ list.count y = 3) ∨ 
    (list.count x = 3 ∧ list.count y = 2)) →
  check_three_and_two list = true :=
  sorry

theorem type_agnostic {α : Type} (list : List α) : 
  check_three_and_two list = true ∨ check_three_and_two list = false :=
  sorry
-- </vc-theorems>