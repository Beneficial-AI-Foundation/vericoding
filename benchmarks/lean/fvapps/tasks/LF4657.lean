-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverse {α : Type} : List α → List α := sorry

theorem reverse_length_preserves {α : Type} (lst : List α) : 
  (reverse lst).length = lst.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_involutive {α : Type} (lst : List α) : 
  reverse (reverse lst) = lst := sorry

theorem reverse_empty {α : Type} : 
  reverse ([] : List α) = [] := sorry

theorem reverse_eq_manual {α : Type} (lst : List α) :
  ∃ manual_reverse : List α → List α, 
    reverse lst = manual_reverse lst := sorry
-- </vc-theorems>