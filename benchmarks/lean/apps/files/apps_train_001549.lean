-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_qaq_subsequences (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_qaq_subsequences_nonnegative (s : String) :
  count_qaq_subsequences s ≥ 0 :=
  sorry

theorem count_qaq_subsequences_lt_two_q (s : String) :
  (s.data.filter (· = 'Q')).length < 2 →
  count_qaq_subsequences s = 0 :=
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_qaq_subsequences "QAQAQYSYIOIWIN"

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_qaq_subsequences "QAQQQZZYNOIWIN"

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_qaq_subsequences "QORZOYAQ"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible