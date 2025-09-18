-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def tram (stops : Nat) (descending : List Nat) (onboarding : List Nat) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem tram_stops_limit (stops : Nat) (descending : List Nat) (onboarding : List Nat)
  (h1 : stops > 0)
  (h2 : stops ≥ max descending.length onboarding.length)
  (h3 : descending.length > 0)
  (h4 : onboarding.length > 0)
  (h5 : ∀ n ∈ descending, n ≥ 0)
  (h6 : ∀ n ∈ onboarding, n ≥ 0) :
  tram stops descending onboarding = tram (stops + 1) descending onboarding :=
sorry
-- </vc-theorems>