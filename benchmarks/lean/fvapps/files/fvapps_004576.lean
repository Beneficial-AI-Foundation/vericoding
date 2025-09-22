-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def new_avg (donations : List Int) (targetAvg : Int) : Option Int :=
  sorry

def list_sum (l : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem new_avg_type_and_positive (donations : List Int) (targetAvg : Int) :
  donations ≠ [] →
  ∀ r : Int, new_avg donations targetAvg = some r →
  r > 0 :=
sorry

theorem new_avg_achieves_target (donations : List Int) (targetAvg : Int) :
  donations ≠ [] →
  ∀ r : Int, new_avg donations targetAvg = some r →
  ((list_sum donations + r) / (donations.length + 1) - targetAvg).natAbs < 1 :=
sorry

theorem new_avg_none_when_negative (donations : List Int) (targetAvg : Int) :
  donations ≠ [] →
  (donations.length + 1) * targetAvg - list_sum donations ≤ 0 →
  new_avg donations targetAvg = none :=
sorry

theorem new_avg_positive_large_target (donations : List Int) (maxDonation : Int) :
  donations ≠ [] →
  (∀ d ∈ donations, d ≥ 0 ∧ d ≤ maxDonation) →
  let targetAvg := maxDonation + 100
  ∀ r : Int, new_avg donations targetAvg = some r →
  r > 0 :=
sorry
-- </vc-theorems>