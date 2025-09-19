-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calc_yoda_teach_probability (n m p k : Nat) : Float := sorry

theorem probability_bounds {n m p k : Nat} (h1: n ≥ 1) (h2: m ≥ 1) (h3: k ≥ 1) (h4: p ≤ k) :
  let prob := calc_yoda_teach_probability n m p k
  0 ≤ prob ∧ prob ≤ 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>