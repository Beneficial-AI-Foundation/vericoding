-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def infected (s : String) : Float := sorry

theorem infected_bounds (s : String) :
  0 ≤ infected s ∧ infected s ≤ 100 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zero_population (s : String) :
  (∀ c, c ∈ s.data → c ≠ '0' ∧ c ≠ '1') →
  infected s = 0 := sorry

theorem all_infected (s : String) :
  (∀ c, c ∈ s.data → c ≠ 'X') →
  ('1' ∈ s.data) →
  infected s = 100 := sorry

theorem ocean_separation (s : String) :
  let lands := s.split (· = 'X')
  let clean_lands := lands.filter (λ land => land.length > 0 ∧ ∀ c, c ∈ land.data → c ≠ '1')
  let infected_lands := lands.filter (λ land => land.length > 0 ∧ ∃ c, c ∈ land.data ∧ c = '1')
  clean_lands.length > 0 →
  infected_lands.length > 0 →
  0 < infected s ∧ infected s < 100 := sorry
-- </vc-theorems>