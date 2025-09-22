-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def search_permMult (nMax: Nat) (k: Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_non_negative {nMax k: Nat} (h1: nMax ≥ 1000) (h2: k ≥ 1) (h3: k ≤ 100) :
  search_permMult nMax k ≥ 0 :=
sorry

theorem monotonic_increasing {nMax1 nMax2 k: Nat} (h1: nMax1 ≥ 1000) (h2: nMax2 ≥ nMax1) (h3: k ≥ 1) (h4: k ≤ 100) :
  search_permMult nMax1 k ≤ search_permMult nMax2 k :=
sorry

theorem k_zero {nMax: Nat} (h1: nMax ≥ 1000) :
  search_permMult nMax 0 = 0 :=
sorry

theorem small_nMax {nMax k: Nat} (h1: nMax ≤ 1000) (h2: k ≥ 0) (h3: k ≤ 100) :
  search_permMult nMax k = 0 :=
sorry
-- </vc-theorems>