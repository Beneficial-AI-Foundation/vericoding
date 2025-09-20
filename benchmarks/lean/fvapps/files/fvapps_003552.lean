-- <vc-preamble>
def count {α : Type} [BEq α] (x : α) (xs : List α) : Nat :=
  xs.filter (· == x) |>.length

/- Test if list is sorted -/

def IsSorted {α : Type} [LE α] : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => x ≤ y ∧ IsSorted (y :: xs)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def modes {α : Type} [Ord α] [BEq α] [LE α] (xs : List α) : List α := sorry

theorem modes_list_sorted {α : Type} [Ord α] [BEq α] [LE α] (xs : List α) (h : xs ≠ []) :
  IsSorted (modes xs) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem modes_elements_in_input {α : Type} [Ord α] [BEq α] [LE α] (xs : List α) (x : α) :
  x ∈ modes xs → x ∈ xs := sorry

theorem modes_counts_equal {α : Type} [Ord α] [BEq α] [LE α] (xs : List α) (h : modes xs ≠ []) :
  ∀ (x y : α), x ∈ modes xs → y ∈ modes xs → count x xs = count y xs := sorry

theorem modes_is_max_count {α : Type} [Ord α] [BEq α] [LE α] (xs : List α) (h : modes xs ≠ []) :
  ∀ (x : α), x ∈ modes xs → ∀ (y : α), y ∈ xs → count x xs ≥ count y xs := sorry

theorem modes_not_min_count {α : Type} [Ord α] [BEq α] [LE α] (xs : List α) (h₁ : modes xs ≠ []) (h₂ : xs ≠ []) :
  ∀ (x : α), x ∈ modes xs → ∃ (y : α), y ∈ xs ∧ count x xs > count y xs := sorry

theorem modes_string_length (s : String) (h : s.length > 0) :
  ∀ (x : Char), x ∈ modes s.data → true := sorry
-- </vc-theorems>