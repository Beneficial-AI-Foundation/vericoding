-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sort_dict (d : Dict) : List (String × Int) := sorry

theorem sort_dict_preserves_items (d : Dict) :
  Dict.mk (sort_dict d) = d := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sort_dict_ordering (d : Dict) (h : (d.items).length ≥ 2) :
  ∀ i : Nat, i < (sort_dict d).length - 1 →
    ((sort_dict d).get! i).2 ≥ ((sort_dict d).get! (i+1)).2 := sorry

theorem sort_dict_length (d : Dict) :
  (sort_dict d).length = d.items.length := sorry

theorem sort_dict_returns_tuples (d : Dict) :
  ∀ x ∈ sort_dict d, ∃ s : String, ∃ n : Int, x = (s, n) := sorry

/-
info: [('1', 3), ('2', 2), ('3', 1)]
-/
-- #guard_msgs in
-- #eval sort_dict {"1": 3, "2": 2, "3": 1}

/-
info: [('3', 6), ('2', 4), ('1', 2)]
-/
-- #guard_msgs in
-- #eval sort_dict {"1": 2, "2": 4, "3": 6}

/-
info: [('a', 6), ('c', 4), ('b', 2)]
-/
-- #guard_msgs in
-- #eval sort_dict {"a": 6, "b": 2, "c": 4}
-- </vc-theorems>