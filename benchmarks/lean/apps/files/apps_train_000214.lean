-- <vc-helpers>
-- </vc-helpers>

def orderlyQueue (s : String) (k : Nat) : String := sorry

private def stringToSortedString (s : String) : String :=
  String.mk (s.data.reverse.reverse) -- placeholder since we can't sort without importing

theorem orderlyQueue_k_gt_one_sorted {s : String} {k : Nat} (h1 : s.length > 0) (h2 : k > 1) :
  orderlyQueue s k = stringToSortedString s := sorry 

theorem orderlyQueue_k_one_length {s : String} (h : s.length > 0) : 
  (orderlyQueue s 1).length = s.length := sorry

theorem orderlyQueue_k_one_chars {s : String} (h : s.length > 0) :
  stringToSortedString (orderlyQueue s 1) = stringToSortedString s := sorry

theorem orderlyQueue_rotation {s : String} {k : Nat} (h1 : s.length > 0) (h2 : k > 0) :
  stringToSortedString (orderlyQueue s k) = stringToSortedString s := sorry

theorem orderlyQueue_k_one_rotation {s : String} (h : s.length > 0) :
  ∃ i, i < s.length ∧ orderlyQueue s 1 = String.mk ((s.data.drop i) ++ (s.data.take i)) := sorry

theorem orderlyQueue_k_one_minimal {s : String} (h : s.length > 0) :
  ∀ i, i < s.length → 
    orderlyQueue s 1 ≤ String.mk ((s.data.drop i) ++ (s.data.take i)) := sorry

/-
info: 'acb'
-/
-- #guard_msgs in
-- #eval orderlyQueue "cba" 1

/-
info: 'aaabc'
-/
-- #guard_msgs in
-- #eval orderlyQueue "baaca" 3

/-
info: 'abcd'
-/
-- #guard_msgs in
-- #eval orderlyQueue "abcd" 2

-- Apps difficulty: interview
-- Assurance level: unguarded