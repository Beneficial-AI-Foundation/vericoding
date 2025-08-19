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
    planets.filter (fun p => planets.idxOf p < maxIdx ∧ minIdx < planets.idxOf p)

-- LLM HELPER
lemma filter_preserves_pairwise (l : List String) (p : String → Bool) :
  l.Pairwise (fun a b => planets.idxOf a < planets.idxOf b) →
  (l.filter p).Pairwise (fun a b => planets.idxOf a < planets.idxOf b) := by
  intro h
  apply List.Pairwise.filter h

-- LLM HELPER
lemma planets_pairwise : planets.Pairwise (fun a b => planets.idxOf a < planets.idxOf b) := by
  simp [planets]
  repeat constructor
  · simp [List.idxOf]; norm_num
  · simp [List.idxOf]; norm_num
  · simp [List.idxOf]; norm_num
  · simp [List.idxOf]; norm_num
  · simp [List.idxOf]; norm_num
  · simp [List.idxOf]; norm_num
  · simp [List.idxOf]; norm_num
  · simp [List.idxOf]; norm_num
  · simp [List.idxOf]; norm_num
  · simp [List.idxOf]; norm_num
  · simp [List.idxOf]; norm_num
  · simp [List.idxOf]; norm_num
  · simp [List.idxOf]; norm_num
  · simp [List.idxOf]; norm_num
  · simp [List.idxOf]; norm_num
  · simp [List.idxOf]; norm_num
  · simp [List.idxOf]; norm_num
  · simp [List.idxOf]; norm_num
  · simp [List.idxOf]; norm_num
  · simp [List.idxOf]; norm_num
  · simp [List.idxOf]; norm_num
  · simp [List.idxOf]; norm_num
  · simp [List.idxOf]; norm_num
  · simp [List.idxOf]; norm_num
  · simp [List.idxOf]; norm_num
  · simp [List.idxOf]; norm_num
  · simp [List.idxOf]; norm_num
  · simp [List.idxOf]; norm_num

-- LLM HELPER
lemma filter_mem_original (l : List String) (p : String → Bool) (x : String) :
  x ∈ l.filter p → x ∈ l := by
  intro h
  exact List.mem_of_mem_filter h

-- LLM HELPER
lemma indexOf_eq_iff_mem_filter (planet : String) (planet1 planet2 : String) :
  planet1 ∈ planets → planet2 ∈ planets →
  let index1 := planets.idxOf planet1
  let index2 := planets.idxOf planet2
  let minIdx := if index1 < index2 then index1 else index2
  let maxIdx := if index1 < index2 then index2 else index1
  (planet ∈ planets.filter (fun p => planets.idxOf p < maxIdx ∧ minIdx < planets.idxOf p)) ↔
  (planet ∈ planets ∧ planets.idxOf planet < maxIdx ∧ minIdx < planets.idxOf planet) := by
  intro h1 h2
  constructor
  · intro h
    constructor
    · exact filter_mem_original planets _ planet h
    · exact (List.mem_filter.mp h).2
  · intro h
    exact List.mem_filter.mpr ⟨h.1, h.2⟩

theorem correctness
(planet1: String)
(planet2: String)
: problem_spec implementation planet1 planet2 := by
  simp [problem_spec, implementation]
  use implementation planet1 planet2
  constructor
  · rfl
  · simp [implementation]
    let planets_def := ["Mercury", "Venus", "Earth", "Mars", "Jupiter", "Saturn", "Uranus", "Neptune"]
    by_cases h : planet1 ∉ planets ∨ planet2 ∉ planets
    · simp [h]
    · simp [h]
      push_neg at h
      constructor
      · intro str hstr
        exact filter_mem_original planets _ str hstr
      · constructor
        · intro planet
          rw [indexOf_eq_iff_mem_filter planet planet1 planet2 h.1 h.2]
          simp
        · exact filter_preserves_pairwise planets _ planets_pairwise