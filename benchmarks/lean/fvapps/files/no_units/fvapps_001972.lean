-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_processing_time (n k : Nat) (contrasts : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_processing_time_nonnegative {n k : Nat} {contrasts : List Nat} 
  (h : k ≤ n) (h2 : n = contrasts.length) :
  min_processing_time n k contrasts ≥ 0 :=
sorry

theorem min_processing_time_upper_bound {n k : Nat} {contrasts : List Nat}
  (h : k ≤ n) (h2 : n = contrasts.length) (h3 : contrasts ≠ [])
  (max : Nat) (min : Nat) (hmax : max ∈ contrasts) (hmin : min ∈ contrasts)
  (hmax_upper : ∀ x ∈ contrasts, x ≤ max) (hmin_lower : ∀ x ∈ contrasts, min ≤ x) :
  min_processing_time n k contrasts ≤ max - min :=
sorry 

theorem min_processing_time_k_equals_n {n : Nat} {contrasts : List Nat}
  (h : n = contrasts.length) (h2 : n ≥ 2)
  (max : Nat) (min : Nat) (hmax : max ∈ contrasts) (hmin : min ∈ contrasts)
  (hmax_upper : ∀ x ∈ contrasts, x ≤ max) (hmin_lower : ∀ x ∈ contrasts, min ≤ x) :
  min_processing_time n n contrasts ≥ 0 ∧ 
  min_processing_time n n contrasts ≤ max - min :=
sorry

theorem min_processing_time_k_equals_one {n : Nat} {contrasts : List Nat} 
  (h : n = contrasts.length) (h2 : n ≥ 2)
  (max : Nat) (min : Nat) (hmax : max ∈ contrasts) (hmin : min ∈ contrasts)
  (hmax_upper : ∀ x ∈ contrasts, x ≤ max) (hmin_lower : ∀ x ∈ contrasts, min ≤ x) :
  min_processing_time n 1 contrasts ≥ 0 ∧
  min_processing_time n 1 contrasts ≤ max - min :=
sorry

theorem min_processing_time_sort_invariant {n k : Nat} {contrasts : List Nat}
  (h : n = contrasts.length) (h2 : n ≥ 2) (h3 : k = max 1 (n/2))
  (sorted_contrasts : List Nat) (h4 : sorted_contrasts.length = contrasts.length)
  (h5 : ∀ x, x ∈ contrasts ↔ x ∈ sorted_contrasts) :
  min_processing_time n k contrasts = min_processing_time n k sorted_contrasts :=
sorry
-- </vc-theorems>