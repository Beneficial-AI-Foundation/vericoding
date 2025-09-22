-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_min_moves (n: Nat) (arr: List Int) : Nat := sorry

theorem find_min_moves_result_range {n: Nat} {arr: List Int} (h: n > 0) :
  find_min_moves n arr ≤ n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_min_moves_result_nonneg {n: Nat} {arr: List Int} :
  find_min_moves n arr ≥ 0 := sorry

theorem find_min_moves_all_same {n: Nat} {v: Int} (h: n > 0) :
  find_min_moves n (List.replicate n v) = 0 := sorry

theorem find_min_moves_single_different {n: Nat} {v w: Int} (h1: n ≥ 2) (h2: v ≠ w) :
  find_min_moves n ([v] ++ List.replicate (n-1) w) = 1 := sorry

theorem find_min_moves_reverse {n: Nat} {arr: List Int} (h: n > 0) :
  find_min_moves n arr = find_min_moves n arr.reverse := sorry
-- </vc-theorems>