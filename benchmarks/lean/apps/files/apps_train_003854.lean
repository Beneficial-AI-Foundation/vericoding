-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countBy (x : Int) (n : Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_by_len {x n : Int} (hx : x > 0) (hn : n > 0) :
  (countBy x n).length = n :=
  sorry

theorem count_by_multiples {x n : Int} (hx : x > 0) (hn : n > 0) :
  ∀ i ∈ countBy x n, i % x = 0 :=
  sorry

theorem count_by_ascending {x n : Int} (hx : x > 0) (hn : n > 0) :
  ∀ (i j : Nat), i < j → j < (countBy x n).length → 
    (countBy x n)[i]! < (countBy x n)[j]! :=
  sorry

theorem count_by_consecutive {x n : Int} (hx : x > 0) (hn : n > 0) :
  ∀ (i : Nat), i + 1 < (countBy x n).length →
    (countBy x n)[i + 1]! - (countBy x n)[i]! = x :=
  sorry

/-
info: [1, 2, 3, 4, 5]
-/
-- #guard_msgs in
-- #eval count_by 1 5

/-
info: [2, 4, 6, 8, 10]
-/
-- #guard_msgs in
-- #eval count_by 2 5

/-
info: [100, 200, 300, 400, 500]
-/
-- #guard_msgs in
-- #eval count_by 100 5
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded