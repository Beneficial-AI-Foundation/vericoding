-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_rectangle_pairs (n : Nat) (rectangles : List (Nat × Nat × Nat)) : Nat :=
  sorry

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
-- </vc-theorems>