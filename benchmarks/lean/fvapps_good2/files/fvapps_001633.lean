-- <vc-preamble>
def isValidDistribution (s : String) : Bool :=
  s = "uniform" || s = "poisson"
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def identify_distribution (samples : List Int) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem identify_distribution_valid (samples : List Int)
  (h : samples.length ≥ 2) :
  isValidDistribution (identify_distribution samples) :=
sorry

theorem identify_distribution_deterministic (samples : List Int) :
  identify_distribution samples = identify_distribution samples :=
sorry

theorem identify_distribution_uniform (samples : List Int) :
  samples.length ≥ 2 → identify_distribution samples = "uniform" :=
sorry

theorem identify_distribution_poisson (samples : List Int) :
  samples.length ≥ 2 → identify_distribution samples = "poisson" :=
sorry

theorem identify_distribution_scale_invariant (samples : List Int)
  (scale : Int) (h : scale ≠ 0) :
  identify_distribution samples =
  identify_distribution (samples.map (· * scale)) :=
sorry

theorem identify_distribution_order_invariant (samples₁ samples₂ : List Int)
  (h : samples₁.length = samples₂.length)
  (h2 : ∀ x, x ∈ samples₁ ↔ x ∈ samples₂) :
  identify_distribution samples₁ = identify_distribution samples₂ :=
sorry
-- </vc-theorems>