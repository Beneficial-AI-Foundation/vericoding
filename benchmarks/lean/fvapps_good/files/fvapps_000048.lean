-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_trades (x y k : Nat) : Nat := sorry

theorem min_trades_nonneg {x y k : Nat} (hx : x ≥ 2) (hy : y ≥ 1) (hk : k ≥ 1) :
  min_trades x y k ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_trades_ge_k {x y k : Nat} (hx : x ≥ 2) (hy : y ≥ 1) (hk : k ≥ 1) :
  min_trades x y k ≥ k := sorry

theorem min_trades_stick_requirement {x y k : Nat} (hx : x ≥ 2) (hy : y ≥ 1) (hk : k ≥ 1) :
  let stick_trades := min_trades x y k - k
  stick_trades * (x - 1) ≥ y * k + k - 1 := sorry

theorem min_trades_minimal {x y k : Nat} (hx : x ≥ 2) (hy : y ≥ 1) (hk : k ≥ 1) :
  let stick_trades := min_trades x y k - k
  stick_trades > 0 →
  (stick_trades - 1) * (x - 1) < y * k + k - 1 := sorry

theorem min_trades_positive {x y k : Nat} (hx : x ≥ 2) (hy : y ≥ 1) (hk : k ≥ 1) :
  min_trades x y k > 0 := sorry

theorem min_trades_nat {x y k : Nat} (hx : x ≥ 2) (hy : y ≥ 1) (hk : k ≥ 1) :
  min_trades x y k = ↑(min_trades x y k) := sorry
-- </vc-theorems>