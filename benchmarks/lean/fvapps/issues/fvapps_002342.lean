-- <vc-preamble>
def List.sum (l : List Int) : Int :=
  sorry

def Nat.toInt (n : Nat) : Int :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_pivot_index (nums : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pivot_index_empty :
  find_pivot_index [] = -1 := sorry

theorem pivot_index_single {n : Int} :
  find_pivot_index [n] = 0 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_pivot_index [1, 7, 3, 6, 5, 6]

/-
info: -1
-/
-- #guard_msgs in
-- #eval find_pivot_index [1, 2, 3]

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_pivot_index [2, 1, -1]
-- </vc-theorems>