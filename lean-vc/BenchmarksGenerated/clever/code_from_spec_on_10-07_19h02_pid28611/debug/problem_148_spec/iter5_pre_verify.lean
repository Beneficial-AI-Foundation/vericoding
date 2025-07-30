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
def planets : List String := ["Mercury", "Venus", "Earth", "Mars", "Jupiter", "Saturn", "Uranus", "Neptune"]

def implementation (planet1: String) (planet2: String) : List String := 
  if planet1 ∉ planets ∨ planet2 ∉ planets then
    []
  else
    let index1 := planets.indexOf planet1
    let index2 := planets.indexOf planet2
    let minIdx := if index1 < index2 then index1 else index2
    let maxIdx := if index1 < index2 then index2 else index1
    planets.filter (fun p => minIdx < planets.indexOf p ∧ planets.indexOf p < maxIdx)

-- LLM HELPER
lemma planets_def : planets = ["Mercury", "Venus", "Earth", "Mars", "Jupiter", "Saturn", "Uranus", "Neptune"] := by
  rfl

-- LLM HELPER
lemma filter_mem_original {α : Type*} (l : List α) (p : α → Bool) : ∀ x ∈ l.filter p, x ∈ l := by
  intros x hx
  exact List.mem_of_mem_filter hx

-- LLM HELPER
lemma filter_sorted {α : Type*} (l : List α) (r : α → α → Prop) (p : α → Bool) : 
  l.Sorted r → (l.filter p).Sorted r := by
  intro h
  exact List.Sorted.filter h p

-- LLM HELPER
lemma planets_sorted : planets.Sorted (fun a b => planets.indexOf a < planets.indexOf b) := by
  rw [planets_def]
  apply List.Sorted.of_pairwise
  apply List.Pairwise.of_forall
  intros i j hij
  cases' i with i
  · simp
  · cases' j with j
    · simp at hij
    · simp [List.indexOf]
      norm_num

-- LLM HELPER
lemma mem_filter_iff {α : Type*} (l : List α) (p : α → Bool) (x : α) : 
  x ∈ l.filter p ↔ x ∈ l ∧ p x = true := by
  exact List.mem_filter

-- LLM HELPER
lemma empty_list_properties : 
  (∀ str ∈ ([] : List String), str ∈ planets) ∧
  (∀ planet ∈ planets, planet ∈ ([] : List String) ↔ False) ∧
  ([] : List String).Sorted (fun a b => planets.indexOf a < planets.indexOf b) := by
  constructor
  · simp
  · constructor
    · simp
    · exact List.Sorted.nil

-- LLM HELPER
lemma decide_eq_true_iff {p : Prop} [Decidable p] : decide p = true ↔ p := by
  exact decide_eq_true_iff

theorem correctness
(planet1: String)
(planet2: String)
: problem_spec implementation planet1 planet2 := by
  unfold problem_spec implementation
  simp only [planets_def]
  use (if planet1 ∉ planets ∨ planet2 ∉ planets then [] else 
        planets.filter (fun p => 
          (if planets.indexOf planet1 < planets.indexOf planet2 then planets.indexOf planet1 else planets.indexOf planet2) < planets.indexOf p ∧ 
          planets.indexOf p < (if planets.indexOf planet1 < planets.indexOf planet2 then planets.indexOf planet2 else planets.indexOf planet1)))
  constructor
  · rfl
  · split_ifs with h
    · simp
      apply empty_list_properties
    · push_neg at h
      have h_both_in : planet1 ∈ planets ∧ planet2 ∈ planets := h
      have h1_in : planet1 ∈ planets := h_both_in.1
      have h2_in : planet2 ∈ planets := h_both_in.2
      constructor
      · intros str hstr
        exact filter_mem_original planets _ str hstr
      · constructor
        · intro planet hplanet
          rw [mem_filter_iff]
          constructor
          · intro h_mem
            constructor
            · exact hplanet
            · rw [decide_eq_true_iff]
              exact h_mem
          · intro h_cond
            exact h_cond.2
        · exact filter_sorted planets (fun a b => planets.indexOf a < planets.indexOf b) _ planets_sorted