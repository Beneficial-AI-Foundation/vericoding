-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def categorize_study (p_value: Float) (requirements: Nat) : String := sorry

theorem categorize_study_returns_valid_category 
  (p_value: Float) (requirements: Nat)
  (h1: 0 < p_value) (h2: p_value ≤ 1) (h3: requirements ≤ 6) :
  (categorize_study p_value requirements = "Fine" ∨ 
   categorize_study p_value requirements = "Needs review" ∨
   categorize_study p_value requirements = "Pants on fire") := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zero_requirements_never_fine
  (p_value: Float)
  (h1: 0 < p_value) (h2: p_value ≤ 1) :
  categorize_study p_value 0 ≠ "Fine" := sorry

theorem study_value_threshold
  (p_value: Float) (requirements: Nat)
  (h1: 0 < p_value) (h2: p_value ≤ 1) (h3: requirements ≤ 6)
  (study_value := p_value * Float.pow 2 (Float.ofNat (6 - requirements))) :
  (study_value ≥ 0.15 → categorize_study p_value requirements = "Pants on fire") ∧
  (study_value < 0.05 ∧ requirements > 0 → categorize_study p_value requirements = "Fine") ∧
  (study_value < 0.05 ∧ requirements = 0 → categorize_study p_value requirements = "Needs review") ∧
  (0.05 ≤ study_value ∧ study_value < 0.15 → categorize_study p_value requirements = "Needs review") := sorry

theorem high_p_values_fail
  (p_value: Float)
  (h1: 0.15 ≤ p_value) (h2: p_value ≤ 1) :
  categorize_study p_value 6 = "Pants on fire" := sorry
-- </vc-theorems>