-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_prime (n : Nat) : Bool :=
  sorry

def color_jewelry (n : Nat) : Nat × List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem k_bounds (n : Nat) (h : n ≥ 1) :
  let (k, colors) := color_jewelry n
  k = 1 ∨ k = 2 :=
sorry

theorem large_n_coloring (n : Nat) (h1 : n > 2) :
  let (k, colors) := color_jewelry n
  k = 2 :=
sorry
-- </vc-theorems>