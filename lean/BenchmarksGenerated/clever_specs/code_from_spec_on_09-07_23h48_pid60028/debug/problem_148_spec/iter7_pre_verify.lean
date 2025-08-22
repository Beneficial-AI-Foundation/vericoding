def problem_spec
(implementation: String → String → List String)
(planet1: String)
(planet2: String) :=
let spec (result: List String) :=
let planets := ["Mercury", "Venus", "Earth", "Mars", "Jupiter", "Saturn", "Uranus", "Neptune"];
if planet1 ∉ planets ∨ planet2 ∉ planets then
  result = []
else
  let index1 := planets.idxOf planet1;
  let index2 := planets.idxOf planet2;
  let minIdx := if index1 < index2 then index1 else index2;
  let maxIdx := if index1 < index2 then index2 else index1;
  (∀ str ∈ result, str ∈ planets) ∧
  (∀ planet ∈ planets, planet ∈ result ↔
    planets.idxOf planet < maxIdx ∧
    minIdx < planets.idxOf planet) ∧
  result.Pairwise (fun a b => planets.idxOf a < planets.idxOf b)
∃ result, implementation planet1 planet2 = result ∧
spec result

-- LLM HELPER
def planets : List String := ["Mercury", "Venus", "Earth", "Mars", "Jupiter", "Saturn", "Uranus", "Neptune"]

def implementation (planet1: String) (planet2: String) : List String :=
  if planet1 ∉ planets ∨ planet2 ∉ planets then
    []
  else
    let index1 := planets.idxOf planet1
    let index2 := planets.idxOf planet2
    let minIdx := if index1 < index2 then index1 else index2
    let maxIdx := if index1 < index2 then index2 else index1
    planets.filter (fun planet => 
      let idx := planets.idxOf planet
      decide (minIdx < idx ∧ idx < maxIdx))

-- LLM HELPER
lemma planets_eq : planets = ["Mercury", "Venus", "Earth", "Mars", "Jupiter", "Saturn", "Uranus", "Neptune"] := rfl

-- LLM HELPER
lemma filter_mem {α : Type*} (p : α → Bool) (l : List α) (x : α) : x ∈ l.filter p → x ∈ l := by
  intro h
  exact List.mem_of_mem_filter h

-- LLM HELPER
lemma filter_prop {α : Type*} (p : α → Bool) (l : List α) (x : α) : x ∈ l.filter p → p x = true := by
  intro h
  exact List.of_mem_filter h

-- LLM HELPER
lemma mem_filter_iff {α : Type*} (p : α → Bool) (l : List α) (x : α) : x ∈ l.filter p ↔ x ∈ l ∧ p x = true := by
  constructor
  · intro h
    exact ⟨filter_mem p l x h, filter_prop p l x h⟩
  · intro ⟨h1, h2⟩
    exact List.mem_filter.mpr ⟨h1, h2⟩

-- LLM HELPER
lemma pairwise_filter_preserves_order : 
  ∀ (minIdx maxIdx : Nat), 
  (planets.filter (fun planet => 
    let idx := planets.idxOf planet
    decide (minIdx < idx ∧ idx < maxIdx))).Pairwise (fun a b => planets.idxOf a < planets.idxOf b) := by
  intro minIdx maxIdx
  apply List.Pairwise.filter
  simp [planets_eq]
  exact List.pairwise_lt_idxOf

-- LLM HELPER
lemma filter_condition_equiv (minIdx maxIdx : Nat) (planet : String) :
  (minIdx < planets.idxOf planet ∧ planets.idxOf planet < maxIdx) ↔
  decide (minIdx < planets.idxOf planet ∧ planets.idxOf planet < maxIdx) = true := by
  simp [decide_eq_true_iff]

theorem correctness
(planet1: String)
(planet2: String)
: problem_spec implementation planet1 planet2 := by
  use implementation planet1 planet2
  constructor
  · rfl
  · simp [problem_spec]
    by_cases h : planet1 ∉ planets ∨ planet2 ∉ planets
    · simp [implementation, h]
    · simp [implementation, h]
      constructor
      · intro str hstr
        have : str ∈ planets := filter_mem _ planets str hstr
        exact this
      · constructor
        · intro planet hplanet
          constructor
          · intro hresult
            rw [List.mem_filter] at hresult
            have : decide (let index1 := planets.idxOf planet1; let index2 := planets.idxOf planet2; let minIdx := if index1 < index2 then index1 else index2; let maxIdx := if index1 < index2 then index2 else index1; minIdx < planets.idxOf planet ∧ planets.idxOf planet < maxIdx) = true := hresult.2
            simp [decide_eq_true_iff] at this
            exact this
          · intro hcond
            rw [List.mem_filter]
            constructor
            · exact hplanet
            · simp [decide_eq_true_iff]
              exact hcond
        · exact pairwise_filter_preserves_order _ _