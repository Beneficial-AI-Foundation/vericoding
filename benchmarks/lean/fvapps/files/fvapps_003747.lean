-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sel_reverse (arr : List α) (length : Nat) : List α :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem length_preservation {α : Type} (arr : List α) (length : Nat) :
  List.length (sel_reverse arr length) = List.length arr :=
sorry

theorem elem_preservation {α : Type} (arr : List α) (length : Nat) (a : α) :
  (a ∈ sel_reverse arr length) ↔ (a ∈ arr) :=
sorry

theorem zero_length {α : Type} (arr : List α) :
  sel_reverse arr 0 = arr :=
sorry

theorem chunk_reversal {α : Type} (arr : List α) (length : Nat) (h : length > 0) :
  ∀ i, i < List.length arr →
  (sel_reverse arr length).get? i =
    arr.get? (i/length * length + (length - 1 - i%length)) :=
sorry

theorem length_one {α : Type} (arr : List α) :
  sel_reverse arr 1 = arr :=
sorry

theorem full_length {α : Type} (arr : List α) (h : arr ≠ []) :
  sel_reverse arr (List.length arr) = arr.reverse :=
sorry
-- </vc-theorems>