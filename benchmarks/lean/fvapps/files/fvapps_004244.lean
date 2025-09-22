-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumToInfinity (sequence : List Float) : Option Float := sorry

theorem geometric_sequence_properties {sequence : List Float}
  (hlen : sequence.length ≥ 4)
  (hfirst : sequence.head! ≠ 0)
  (hratio : ∀ i, i < sequence.length - 1 →
    (sequence.get! (i+1) / sequence.get! i).abs < 0.99) :
  ∃ (result : Float),
    sumToInfinity sequence = some result ∧
    ¬ result.isNaN := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_ratio_no_solution {sequence : List Float}
  (hlen : sequence.length = 4)
  (hfirst : sequence.head! ≠ 0)
  (hratio : (sequence.get! 1 / sequence.get! 0).abs ≥ 1) :
  sumToInfinity sequence = none := sorry

theorem basic_convergence :
  sumToInfinity [1, 0.5, 0.25, 0.125] = some 2.0 := sorry
-- </vc-theorems>