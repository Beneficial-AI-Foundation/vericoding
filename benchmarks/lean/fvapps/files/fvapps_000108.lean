-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_peaks (window : List Nat) : Nat :=
  sorry

def solve_door_peaks (n k : Nat) (arr : List Nat) : Nat × Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem peaks_atleast_one {n k : Nat} {arr : List Nat}
  (h1 : n ≥ 3)
  (h2 : k ≥ 3)
  (h3 : k ≤ n)
  (h4 : arr.length = n) :
  let (peaks, _) := solve_door_peaks n k arr
  peaks ≥ 1 :=
sorry

theorem position_in_range {n k : Nat} {arr : List Nat}
  (h1 : n ≥ 3)
  (h2 : k ≥ 3)
  (h3 : k ≤ n)
  (h4 : arr.length = n) :
  let (_, pos) := solve_door_peaks n k arr
  1 ≤ pos ∧ pos ≤ n - k + 1 :=
sorry

theorem peaks_match_window {n k : Nat} {arr : List Nat}
  (h1 : n ≥ 3)
  (h2 : k ≥ 3)
  (h3 : k ≤ n)
  (h4 : arr.length = n) :
  let (peaks, pos) := solve_door_peaks n k arr
  let window := arr.take k
  count_peaks window = peaks - 1 :=
sorry
-- </vc-theorems>