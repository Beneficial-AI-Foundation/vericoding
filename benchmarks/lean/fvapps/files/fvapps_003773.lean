-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def last {α : Type} : α → α := sorry
def last_list {α : Type} : List α → α := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem last_list_property {α : Type} (l : List α) (h : l ≠ []) :
  ∃ x, last_list l = x := sorry

theorem last_vararg_property {α : Type} (l : List α) (h : l ≠ []) :
  ∃ x, last l.head = x := sorry

theorem last_string_property (s : String) (h : s.length > 0) :
  ∃ c, last_list s.data = c := sorry

theorem last_tuple_property {α : Type} (a b c d : α) :
  last d = d := sorry

theorem last_single_property {α : Type} (x : α) :
  last x = x := sorry
-- </vc-theorems>