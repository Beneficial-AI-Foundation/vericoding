-- <vc-helpers>
-- </vc-helpers>

def calculate_probability (S N M K : Nat) : Float := sorry

theorem equal_sizes {S : Nat}
  (h1: S ≥ 1)
  (h2: S ≤ 20) :
  let p := calculate_probability S S S 0
  (p - 1).abs < 0.000001 := sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible