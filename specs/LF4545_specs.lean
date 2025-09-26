-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check (seq : List α) (elem : α) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_membership_true {α} (seq : List α) (elem : α) :
  elem ∈ seq → check seq elem = true := by
  sorry

theorem check_membership_false {α} (seq : List α) (elem : α) :
  elem ∉ seq → check seq elem = false := by
  sorry

theorem check_reflexive {α} (seq : List α) (elem : α) :
  check (seq ++ [elem]) elem = true := by
  sorry

end CheckSequence

/-
info: True
-/
-- #guard_msgs in
-- #eval check [1, 2, 3] 2

/-
info: False
-/
-- #guard_msgs in
-- #eval check ["hello", "world"] "cat"

/-
info: True
-/
-- #guard_msgs in
-- #eval check [66.25, 333, 333.5] 333
-- </vc-theorems>