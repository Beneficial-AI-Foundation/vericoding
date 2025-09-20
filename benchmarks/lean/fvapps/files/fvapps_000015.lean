-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_window_size (a b x y : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_window_size_corners (a b : Nat) (ha : a ≥ 2) (hb : b ≥ 2)
    (ha2 : a ≤ 1000) (hb2 : b ≤ 1000) :
    let corner_result := max ((a-1)*b) ((b-1)*a);
    max_window_size a b 0 0 = corner_result ∧
    max_window_size a b (a-1) 0 = corner_result ∧
    max_window_size a b 0 (b-1) = corner_result ∧
    max_window_size a b (a-1) (b-1) = corner_result :=
  sorry

theorem max_window_size_square_symmetry (n : Nat) (hn1 : n > 0) (hn2 : n ≤ 1000) :
    max_window_size n n 0 1 = max_window_size n n 1 0 ∧
    max_window_size n n (n/2) (n/2) = max_window_size n n (n/2) (n/2) :=
  sorry
-- </vc-theorems>