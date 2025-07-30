def problem_spec
(implementation: String → String → List String)
(planet1: String)
(planet2: String) :=
let spec (result: List String) :=
let planets := ["Mercury", "Venus", "Earth", "Mars", "Jupiter", "Saturn", "Uranus", "Neptune"];
if planet1 ∉ planets ∨ planet2 ∉ planets then
  result = []
else
  let index1 := planets.indexOf planet1;
  let index2 := planets.indexOf planet2;
  let minIdx := if index1 < index2 then index1 else index2;
  let maxIdx := if index1 < index2 then index2 else index1;
  (∀ str ∈ result, str ∈ planets) ∧
  (∀ planet ∈ planets, planet ∈ result ↔
    planets.indexOf planet < maxIdx ∧
    minIdx < planets.indexOf planet) ∧
  result.Sorted (fun a b => planets.indexOf a < planets.indexOf b)
∃ result, implementation planet1 planet2 = result ∧
spec result

-- LLM HELPER
def planets : List String := ["Mercury", "Venus", "Earth", "Mars", "Jupiter", "Saturn", "Uranus", "Neptune"]

def implementation (planet1: String) (planet2: String) : List String :=
  if planet1 ∉ planets ∨ planet2 ∉ planets then
    []
  else
    let index1 := planets.indexOf planet1
    let index2 := planets.indexOf planet2
    let minIdx := if index1 < index2 then index1 else index2
    let maxIdx := if index1 < index2 then index2 else index1
    planets.filter (fun planet => 
      let idx := planets.indexOf planet
      minIdx < idx ∧ idx < maxIdx)

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
lemma sorted_filter_preserves_order : 
  ∀ (minIdx maxIdx : Nat), 
  (planets.filter (fun planet => 
    let idx := planets.indexOf planet
    minIdx < idx ∧ idx < maxIdx)).Sorted (fun a b => planets.indexOf a < planets.indexOf b) := by
  intro minIdx maxIdx
  apply List.Sorted.filter
  · intro a b c hab hbc
    exact Nat.lt_trans hab hbc
  · apply List.pairwise_of_sorted
    simp [planets_eq]
    norm_num

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
            rw [mem_filter_iff] at hresult
            simp at hresult
            exact hresult.2
          · intro hcond
            rw [mem_filter_iff]
            simp
            exact ⟨hplanet, hcond⟩
        · exact sorted_filter_preserves_order _ _