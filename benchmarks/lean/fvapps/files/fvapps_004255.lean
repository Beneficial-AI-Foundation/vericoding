-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum_consecutives (xs : List Int) : List Int := sorry

theorem sum_consecutives_length 
  (xs : List Int) 
  (h : xs ≠ []) : 
  List.length (sum_consecutives xs) ≤ List.length xs :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_consecutives_preserves_elements
  (xs : List Int)
  (h : xs ≠ []) :
  List.foldl (· + ·) 0 (sum_consecutives xs) = List.foldl (· + ·) 0 xs :=
sorry

theorem single_element_unchanged 
  (xs : List Int)
  (h : List.length xs = 1) :
  sum_consecutives xs = xs :=
sorry

theorem identical_elements
  (n : Nat)
  (h : n > 0)
  (xs : List Int)
  (h2 : xs.length = n)
  (h3 : ∀ x ∈ xs, x = 0) :
  (sum_consecutives xs).length = 1 ∧ 
  (sum_consecutives xs).head! = List.foldl (· + ·) 0 xs :=
sorry

theorem alternating_elements_preserve_length
  (xs : List Int)
  (h : xs.length ≥ 2)
  (h2 : ∀ (i : Nat), i + 1 < xs.length → 
        xs.get! i ≠ xs.get! (i + 1)) :
  (sum_consecutives xs).length = xs.length :=
sorry
-- </vc-theorems>