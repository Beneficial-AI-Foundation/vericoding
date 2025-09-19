-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def interest (principal : Int) (rate : Float) (periods : Int) : List Int := sorry

theorem interest_basic_structure 
  (principal : Int) (rate : Float) (periods : Int)
  (h1 : principal > 0) (h2 : principal ≤ 1000000)
  (h3 : rate > 0) (h4 : rate ≤ 1)
  (h5 : periods ≥ 0) (h6 : periods ≤ 100) :
  let result := interest principal rate periods
  (result.length = 2) ∧ 
  (∀ x ∈ result, x ≥ 0) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem simple_less_than_compound
  (principal : Int) (rate : Float) (periods : Int)
  (h1 : principal > 0) (h2 : principal ≤ 1000000)
  (h3 : rate > 0) (h4 : rate ≤ 1)
  (h5 : periods ≥ 0) (h6 : periods ≤ 100) :
  let result := interest principal rate periods
  have h7 : result.length = 2 := sorry
  result.get ⟨0, by simp [h7]⟩ ≤ result.get ⟨1, by simp [h7]⟩ :=
sorry

theorem zero_periods_returns_principal
  (principal : Int) (rate : Float)
  (h1 : principal > 0) (h2 : principal ≤ 1000000)
  (h3 : rate > 0) (h4 : rate ≤ 1) :
  let result := interest principal rate 0
  have h5 : result.length = 2 := sorry
  (result.get ⟨0, by simp [h5]⟩ = principal) ∧ 
  (result.get ⟨1, by simp [h5]⟩ = principal) :=
sorry

theorem compound_grows_faster
  (principal : Int) (rate : Float) (periods : Int)
  (h1 : principal > 0) (h2 : principal ≤ 1000000)
  (h3 : rate > 0) (h4 : rate ≤ 1)
  (h5 : periods > 1) (h6 : periods ≤ 100) :
  let result := interest principal rate periods
  have h7 : result.length = 2 := sorry
  let simple_growth := result.get ⟨0, by simp [h7]⟩ - principal
  let compound_growth := result.get ⟨1, by simp [h7]⟩ - principal
  compound_growth ≥ simple_growth :=
sorry

theorem one_period_equality
  (principal : Int) (rate : Float)
  (h1 : principal > 0) (h2 : principal ≤ 1000000)
  (h3 : rate > 0) (h4 : rate ≤ 1) :
  let result := interest principal rate 1
  have h5 : result.length = 2 := sorry
  result.get ⟨0, by simp [h5]⟩ = result.get ⟨1, by simp [h5]⟩ :=
sorry

theorem zero_rate_returns_principal
  (principal : Int) (periods : Int)
  (h1 : principal > 0) (h2 : principal ≤ 1000000)
  (h3 : periods ≥ 0) (h4 : periods ≤ 100) :
  let result := interest principal 0 periods
  have h5 : result.length = 2 := sorry
  (result.get ⟨0, by simp [h5]⟩ = principal) ∧ 
  (result.get ⟨1, by simp [h5]⟩ = principal) :=
sorry
-- </vc-theorems>