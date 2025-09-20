-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pi : Float := 3.14159265359
def iter_pi (epsilon : Float) : List Float := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem iter_pi_result_format {ε : Float} (h : ε > 0) (h2 : ε ≤ 0.1) :
  let result := iter_pi ε
  result.length = 2 ∧ 
  result.head! > 0 ∧
  (result.get! 1 - pi).abs ≤ ε := sorry

theorem iter_pi_converges {ε : Float} (h : ε > 0) (h2 : ε ≤ 0.1) :
  let result := iter_pi ε
  (result.get! 1 - pi).abs ≤ ε := sorry

theorem iter_pi_decimal_places {ε : Float} (h : ε > 0) (h2 : ε ≤ 0.1) :
  let result := iter_pi ε
  result.get! 1 = result.get! 1 := sorry
-- </vc-theorems>