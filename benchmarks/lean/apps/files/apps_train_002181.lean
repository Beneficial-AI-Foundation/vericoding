-- <vc-preamble>
def count_rectangle_pairs (n : Nat) (rectangles : List (Nat × Nat × Nat)) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sqrt (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem non_negative_result (n : Nat) (rectangles : List (Nat × Nat × Nat)) :
  count_rectangle_pairs n rectangles ≥ 0 :=
  sorry

theorem single_rect_count (rect : Nat × Nat × Nat) (count : Nat) 
    (h : rect.2.2 = count) :
  let factors := (List.range (sqrt count)).filter (fun i => count % i = 0)
  count_rectangle_pairs 1 [rect] = if sqrt count * sqrt count = count 
    then 2 * factors.length - 1
    else 2 * factors.length :=
  sorry

theorem result_bounded_by_min_count (n : Nat) (rectangles : List (Nat × Nat × Nat))
    (h : rectangles ≠ []) : 
  count_rectangle_pairs n rectangles ≤ 
    List.foldl Nat.min ((List.head! rectangles).2.2) 
      (List.tail! rectangles |>.map (fun r => r.2.2)) :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_rectangle_pairs 1 [(1, 1, 9)]

/-
info: 6
-/
-- #guard_msgs in
-- #eval count_rectangle_pairs 2 [(2, 3, 20), (2, 4, 40)]

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_rectangle_pairs 2 [(1, 2, 5), (2, 3, 5)]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded