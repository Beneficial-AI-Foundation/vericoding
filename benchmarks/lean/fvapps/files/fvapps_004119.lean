-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rectangles (n m : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rectangles_symmetry
  (n m : Nat)
  (h1 : n ≥ 2)
  (h2 : m ≥ 2) :
  rectangles n m = rectangles m n :=
  sorry

theorem rectangles_non_negative
  (n m : Nat)
  (h1 : n ≥ 2)
  (h2 : m ≥ 2) :
  rectangles n m ≥ 0 :=
  sorry

theorem rectangles_single_line_n
  (n : Nat)
  (h : n ≥ 1) :
  rectangles 1 n = 0 :=
  sorry

theorem rectangles_single_line_m
  (n : Nat)
  (h : n ≥ 1) :
  rectangles n 1 = 0 :=
  sorry

theorem rectangles_monotonic_n
  (n m : Nat)
  (h1 : n ≥ 2)
  (h2 : m ≥ 2) :
  rectangles (n + 1) m ≥ rectangles n m :=
  sorry

theorem rectangles_monotonic_m
  (n m : Nat)
  (h1 : n ≥ 2)
  (h2 : m ≥ 2) :
  rectangles n (m + 1) ≥ rectangles n m :=
  sorry
-- </vc-theorems>