/-
As a member of the editorial board of the prestigous scientific Journal _Proceedings of the National Academy of Sciences_, you've decided to go back and review how well old articles you've published stand up to modern publication best practices. Specifically, you'd like to re-evaluate old findings in light of recent literature about ["researcher degrees of freedom"](http://journals.sagepub.com/doi/full/10.1177/0956797611417632).

You want to categorize all the old articles into three groups: "Fine", "Needs review" and "Pants on fire".

In order to categorize them you've enlisted an army of unpaid grad students to review and give you two data points from each study: (1) the p-value behind the paper's primary conclusions, and (2) the number of recommended author requirements to limit researcher degrees of freedom the authors satisfied:

    * Authors must decide the rule for terminating data collection before data collection begins and report this rule in the article.
    * Authors must collect at least 20 observations per cell or else provide a compelling cost-of-data-collection justification. 
    * Authors must list all variables collected in a study.
    * Authors must report all experimental conditions, including failed manipulations.
    * If observations are eliminated, authors must also report what the statistical results are if those observations are included.
    * If an analysis includes a covariate, authors must report the statistical results of the analysis without the covariate.

Your army of tenure-hungry grad students will give you the p-value as a float between `1.0` and `0.0` exclusive, and the number of author requirements satisfied as an integer from `0` through `6` inclusive.

You've decided to write a function, `categorize_study()` to automatically categorize each study based on these two inputs using the completely scientifically legitimate "bs-factor". The bs-factor for a particular paper is calculated as follows:

 * bs-factor when the authors satisfy all six requirements is 1
 * bs-factor when the authors satisfy only five requirements is 2
 * bs-factor when the authors satisfy only four requirements is 4
 * bs-factor when the authors satisfy only three requirements is 8...

Your function should multiply the p-value by the bs-factor and use that product to return one of the following strings:

 * product is less than 0.05: "Fine"
 * product is 0.05 to 0.15: "Needs review"
 * product is 0.15 or higher: "Pants on fire"

You've also decided that all studies meeting _none_ of the author requirements that would have been categorized as "Fine" should instead be categorized as "Needs review".

For example:

`categorize_study(0.01, 3)` should return `"Needs review"` because the p-value times the bs-factor is `0.08`.

`categorize_study(0.04, 6)` should return `"Fine"` because the p-value times the bs-factor is only `0.04`.

`categorize_study(0.0001, 0)` should return `"Needs review"` even though the p-value times the bs-factor is only `0.0064`.

`categorize_study(0.012, 0)` should return `"Pants on fire"` because the p-value times the bs-factor is `0.768`.
-/

-- <vc-helpers>
-- </vc-helpers>

def categorize_study (p_value: Float) (requirements: Nat) : String := sorry

theorem categorize_study_returns_valid_category 
  (p_value: Float) (requirements: Nat)
  (h1: 0 < p_value) (h2: p_value ≤ 1) (h3: requirements ≤ 6) :
  (categorize_study p_value requirements = "Fine" ∨ 
   categorize_study p_value requirements = "Needs review" ∨
   categorize_study p_value requirements = "Pants on fire") := sorry

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

/-
info: 'Needs review'
-/
-- #guard_msgs in
-- #eval categorize_study 0.01 3

/-
info: 'Fine'
-/
-- #guard_msgs in
-- #eval categorize_study 0.04 6

/-
info: 'Needs review'
-/
-- #guard_msgs in
-- #eval categorize_study 0.0001 0

/-
info: 'Pants on fire'
-/
-- #guard_msgs in
-- #eval categorize_study 0.012 0

-- Apps difficulty: introductory
-- Assurance level: unguarded