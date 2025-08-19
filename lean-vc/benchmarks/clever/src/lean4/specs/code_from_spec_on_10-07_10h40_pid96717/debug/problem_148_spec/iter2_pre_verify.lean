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

-- LLM HELPER
def planets_list : List String := ["Mercury", "Venus", "Earth", "Mars", "Jupiter", "Saturn", "Uranus", "Neptune"]

-- LLM HELPER
def get_planets_between (planet1: String) (planet2: String) : List String :=
  let planets := planets_list
  if planet1 ∉ planets ∨ planet2 ∉ planets then
    []
  else
    let index1 := planets.indexOf planet1
    let index2 := planets.indexOf planet2
    let minIdx := if index1 < index2 then index1 else index2
    let maxIdx := if index1 < index2 then index2 else index1
    planets.filter (fun p => 
      let idx := planets.indexOf p
      minIdx < idx ∧ idx < maxIdx)

def implementation (planet1: String) (planet2: String) : List String := 
  get_planets_between planet1 planet2

-- LLM HELPER
lemma planets_list_eq : planets_list = ["Mercury", "Venus", "Earth", "Mars", "Jupiter", "Saturn", "Uranus", "Neptune"] := by
  rfl

-- LLM HELPER
lemma filter_mem_planets (planet1 planet2 : String) :
  ∀ str ∈ get_planets_between planet1 planet2, str ∈ planets_list := by
  intro str hstr
  unfold get_planets_between at hstr
  by_cases h : planet1 ∉ planets_list ∨ planet2 ∉ planets_list
  · simp [h] at hstr
  · simp [h] at hstr
    exact List.of_mem_filter hstr

-- LLM HELPER
lemma filter_sorted (planet1 planet2 : String) :
  (get_planets_between planet1 planet2).Sorted (fun a b => planets_list.indexOf a < planets_list.indexOf b) := by
  unfold get_planets_between
  by_cases h : planet1 ∉ planets_list ∨ planet2 ∉ planets_list
  · simp [h]
    exact List.Sorted.nil
  · simp [h]
    have : planets_list.Sorted (fun a b => planets_list.indexOf a < planets_list.indexOf b) := by
      apply List.Sorted.of_lt_of_le
      · intro i j h
        exact Nat.lt_trans h (Nat.lt_succ_self j)
      · intro i j h
        exact Nat.le_of_lt h
    exact List.Sorted.filter this

-- LLM HELPER
lemma filter_characterization (planet1 planet2 : String) :
  let planets := planets_list
  ¬(planet1 ∉ planets ∨ planet2 ∉ planets) →
  let index1 := planets.indexOf planet1
  let index2 := planets.indexOf planet2
  let minIdx := if index1 < index2 then index1 else index2
  let maxIdx := if index1 < index2 then index2 else index1
  ∀ planet ∈ planets, planet ∈ get_planets_between planet1 planet2 ↔
    planets.indexOf planet < maxIdx ∧ minIdx < planets.indexOf planet := by
  intro h planet hplanet
  unfold get_planets_between
  simp [h]
  constructor
  · intro hmem
    exact List.mem_filter.mp hmem |>.2
  · intro hcond
    exact List.mem_filter.mpr ⟨hplanet, hcond⟩

theorem correctness
(planet1: String)
(planet2: String)
: problem_spec implementation planet1 planet2 := by
  unfold problem_spec implementation
  use get_planets_between planet1 planet2
  constructor
  · rfl
  · unfold get_planets_between
    simp only [planets_list_eq]
    by_cases h : planet1 ∉ planets_list ∨ planet2 ∉ planets_list
    · simp [h]
    · simp [h]
      constructor
      · exact filter_mem_planets planet1 planet2
      constructor
      · exact filter_characterization planet1 planet2 h
      · exact filter_sorted planet1 planet2