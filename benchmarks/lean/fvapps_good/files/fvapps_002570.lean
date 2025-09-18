-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def square_sum (xs : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem square_sum_nonnegative (xs : List Int) :
  square_sum xs ≥ 0 :=
  sorry

theorem square_sum_empty :
  square_sum [] = 0 :=
  sorry

theorem square_sum_singleton (x : Int) :
  square_sum [x] = x * x :=
  sorry

theorem square_sum_sign_invariant (xs : List Int) :
  square_sum xs = square_sum (xs.map (fun x => -x)) :=
  sorry

theorem square_sum_perm_invariant (xs ys : List Int) :
  List.length xs = List.length ys → square_sum xs = square_sum ys :=
  sorry

theorem square_sum_monotonic_nonneg (xs : List Int) (n : Int) :
  (∀ x ∈ xs, x ≥ 0) → n ≥ 0 → square_sum (n::xs) ≥ square_sum xs :=
  sorry
-- </vc-theorems>