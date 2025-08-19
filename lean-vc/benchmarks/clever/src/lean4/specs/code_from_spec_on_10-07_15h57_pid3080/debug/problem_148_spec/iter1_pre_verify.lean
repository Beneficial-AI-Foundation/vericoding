import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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

def implementation (planet1: String) (planet2: String) : List String :=
  let planets := ["Mercury", "Venus", "Earth", "Mars", "Jupiter", "Saturn", "Uranus", "Neptune"]
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
lemma filter_mem_iff {α : Type*} (l : List α) (p : α → Bool) (x : α) : 
  x ∈ l.filter p ↔ x ∈ l ∧ p x := by
  exact List.mem_filter

-- LLM HELPER
lemma indexOf_mem_lt {α : Type*} [DecidableEq α] (l : List α) (x : α) :
  x ∈ l → l.indexOf x < l.length := by
  exact List.indexOf_lt_length.mpr

-- LLM HELPER
lemma filter_sorted {α : Type*} (l : List α) (p : α → Bool) (r : α → α → Prop) :
  l.Sorted r → (l.filter p).Sorted r := by
  intro h
  exact List.Sorted.filter h

theorem correctness
(planet1: String)
(planet2: String)
: problem_spec implementation planet1 planet2 := by
  unfold problem_spec implementation
  simp only [exists_prop]
  let planets := ["Mercury", "Venus", "Earth", "Mars", "Jupiter", "Saturn", "Uranus", "Neptune"]
  by_cases h : planet1 ∉ planets ∨ planet2 ∉ planets
  · use []
    simp [h]
  · push_neg at h
    obtain ⟨h1, h2⟩ := h
    let index1 := planets.indexOf planet1
    let index2 := planets.indexOf planet2
    let minIdx := if index1 < index2 then index1 else index2
    let maxIdx := if index1 < index2 then index2 else index1
    let result := planets.filter (fun planet => 
      let idx := planets.indexOf planet
      minIdx < idx ∧ idx < maxIdx)
    use result
    constructor
    · simp [h1, h2]
    · simp [h1, h2]
      constructor
      · intro str hstr
        rw [filter_mem_iff] at hstr
        exact hstr.1
      · constructor
        · intro planet hplanet
          rw [filter_mem_iff]
          constructor
          · intro h_filter
            obtain ⟨_, h_cond⟩ := h_filter
            simp at h_cond
            exact h_cond
          · intro h_cond
            constructor
            · exact hplanet
            · simp
              exact h_cond
        · apply filter_sorted
          simp [List.sorted_cons, List.sorted_nil]
          sorry