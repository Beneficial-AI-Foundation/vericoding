-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_vaccine_days (d1 v1 d2 v2 p : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_vaccine_days_min_day
  (d1 v1 d2 v2 p : Nat)
  (h1 : d1 > 0) (h2 : v1 > 0) (h3 : d2 > 0) (h4 : v2 > 0) (h5 : p > 0) :
  find_vaccine_days d1 v1 d2 v2 p ≥ min d1 d2 :=
  sorry

theorem find_vaccine_days_positive 
  (d1 v1 d2 v2 p : Nat)
  (h1 : d1 > 0) (h2 : v1 > 0) (h3 : d2 > 0) (h4 : v2 > 0) (h5 : p > 0) :
  find_vaccine_days d1 v1 d2 v2 p > 0 :=
  sorry

theorem find_vaccine_days_meets_population
  (d1 v1 d2 v2 p : Nat)
  (h1 : d1 > 0) (h2 : v1 > 0) (h3 : d2 > 0) (h4 : v2 > 0) (h5 : p > 0) :
  let result := find_vaccine_days d1 v1 d2 v2 p 
  let vaccines_per_day := (if result ≥ d1 then v1 else 0) + (if result ≥ d2 then v2 else 0)
  let total_vaccinated := vaccines_per_day * (result - min d1 d2 + 1)
  total_vaccinated ≥ p :=
  sorry

theorem find_vaccine_days_identical_schedules
  (d v p : Nat)
  (h1 : d > 0) (h2 : v > 0) (h3 : p > 0) :
  find_vaccine_days d v d v p = find_vaccine_days d (2*v) (d+100) 0 p :=
  sorry
-- </vc-theorems>