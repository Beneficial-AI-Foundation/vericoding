-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_shortest_paths (n m x1 y1 x2 y2 : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_shortest_paths_non_negative
  (n m x1 y1 x2 y2 : Nat)
  (hn : n > 0)
  (hm : m > 0)
  (hx1 : x1 ≤ n)
  (hy1 : y1 ≤ m)
  (hx2 : x2 ≤ n) 
  (hy2 : y2 ≤ m) :
  count_shortest_paths n m x1 y1 x2 y2 ≥ 0 :=
sorry

theorem count_shortest_paths_upper_bound
  (n m x1 y1 x2 y2 : Nat)
  (hn : n > 0)
  (hm : m > 0)
  (hx1 : x1 ≤ n)
  (hy1 : y1 ≤ m)
  (hx2 : x2 ≤ n)
  (hy2 : y2 ≤ m) :
  count_shortest_paths n m x1 y1 x2 y2 < 998244353 :=
sorry

theorem count_shortest_paths_known_case :
  count_shortest_paths 3 3 1 1 1 2 = 5 :=
sorry
-- </vc-theorems>