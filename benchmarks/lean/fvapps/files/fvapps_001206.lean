-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverse_list {α : Type} (xs : List α) : List α :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_list_involution {α : Type} (xs : List α) :
  reverse_list (reverse_list xs) = xs :=
  sorry

theorem reverse_list_length {α : Type} (xs : List α) :
  (reverse_list xs).length = xs.length :=
  sorry

theorem reverse_list_empty {α : Type} :
  @reverse_list α [] = [] :=
  sorry

theorem reverse_list_index {α : Type} (xs : List α) (i : Nat) (h : i < xs.length) :
  (reverse_list xs).get ⟨i, by rw [reverse_list_length]; exact h⟩ = 
  xs.get ⟨xs.length - 1 - i, sorry⟩ :=
  sorry
-- </vc-theorems>