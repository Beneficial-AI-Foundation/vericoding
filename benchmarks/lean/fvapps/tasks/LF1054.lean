-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def total_money : Float := 1000000000.0

def solve_division (m : Nat) (p : Float) : Float × Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_division_sums_to_total (m : Nat) (p : Float)
  (h1 : m ≥ 1) (h2 : m ≤ 100)
  (h3 : p > 0.000001) (h4 : p < 0.999999) :
  let (chef, other) := solve_division m p
  Float.abs (chef + other - total_money) < 0.01 := sorry

theorem solve_division_non_negative (m : Nat) (p : Float)
  (h1 : m ≥ 1) (h2 : m ≤ 100)
  (h3 : p > 0.000001) (h4 : p < 0.999999) :
  let (chef, other) := solve_division m p
  chef ≥ 0 ∧ other ≥ 0 := sorry

theorem solve_division_m_one (p : Float)
  (h1 : p > 0.000001) (h2 : p < 0.999999) :
  let (chef, other) := solve_division 1 p
  Float.abs (chef - total_money) < 0.01 ∧ Float.abs other < 0.01 := sorry

theorem solve_division_bounds (m : Nat) (p : Float)
  (h1 : m ≥ 1) (h2 : m ≤ 100)
  (h3 : p > 0.000001) (h4 : p < 0.999999) :
  let (chef, other) := solve_division m p
  chef ≤ total_money ∧ other ≤ total_money := sorry
-- </vc-theorems>