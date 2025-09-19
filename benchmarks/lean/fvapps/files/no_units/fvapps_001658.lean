-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mod : Nat := 12345787

def circular_limited_sums (max_n: Nat) (max_fn: Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem circular_limited_sums_deterministic  
  (max_n: Nat) (max_fn: Nat)
  (h1: 1 ≤ max_n) (h2: max_n ≤ 50)
  (h3: 1 ≤ max_fn) (h4: max_fn ≤ 5) :
  circular_limited_sums max_n max_fn = circular_limited_sums max_n max_fn :=
sorry

theorem circular_limited_sums_sequence_growth
  (n1 n2 max_fn: Nat)
  (h1: 1 ≤ n1) (h2: n1 < n2) (h3: n2 ≤ 5)
  (h4: 1 ≤ max_fn) (h5: max_fn ≤ 5) :
  circular_limited_sums n1 max_fn < circular_limited_sums n2 max_fn :=
sorry
-- </vc-theorems>