-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_compression_length (n k : Nat) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem compression_length_positive (n k : Nat) (h1 : n > 0) (h2 : k > 0) :
  calculate_compression_length n k > 0 :=
  sorry

theorem compression_length_upper_bound (n k : Nat) (h1 : n > 0) (h2 : k > 0) :
  calculate_compression_length n k ≤ Float.ofNat (2 * n) :=
  sorry

theorem compression_length_monotonic (n k : Nat) (h1 : n > 0) (h2 : k > 0) :
  calculate_compression_length (n + 1) k ≥ calculate_compression_length n k :=
  sorry

theorem compression_length_k_one (n : Nat) (h : n > 0) :
  (calculate_compression_length n 1 - 2).abs < 0.01 :=
  sorry
-- </vc-theorems>