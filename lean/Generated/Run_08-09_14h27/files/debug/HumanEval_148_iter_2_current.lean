import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (planet1: String) (planet2: String) : List String :=
  let planets := ["Mercury", "Venus", "Earth", "Mars", "Jupiter", "Saturn", "Uranus", "Neptune"]
  if planet1 ∉ planets ∨ planet2 ∉ planets then
    []
  else
    let index1 := planets.idxOf planet1
    let index2 := planets.idxOf planet2
    let minIdx := if index1 < index2 then index1 else index2
    let maxIdx := if index1 < index2 then index2 else index1
    planets.filter (fun planet => minIdx < planets.idxOf planet ∧ planets.idxOf planet < maxIdx)

def problem_spec
-- function signature
(impl: String → String → List String)
-- inputs
(planet1: String)
(planet2: String) :=
-- spec
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
  result.Sorted (fun a b => planets.idxOf a < planets.idxOf b)
-- program termination
∃ result, impl planet1 planet2 = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma planets_sorted : 
  let planets := ["Mercury", "Venus", "Earth", "Mars", "Jupiter", "Saturn", "Uranus", "Neptune"]
  planets.Sorted (fun a b => planets.idxOf a < planets.idxOf b) := by
  simp [List.Sorted, List.Pairwise]
  sorry

-- LLM HELPER  
lemma filter_preserves_order (l : List String) (p : String → Bool) :
  l.Sorted (fun a b => l.idxOf a < l.idxOf b) →
  (l.filter p).Sorted (fun a b => l.idxOf a < l.idxOf b) := by
  intro h
  sorry

theorem correctness
(planet1: String)
(planet2: String)
: problem_spec implementation planet1 planet2 := by
  unfold problem_spec implementation
  use (let planets := ["Mercury", "Venus", "Earth", "Mars", "Jupiter", "Saturn", "Uranus", "Neptune"]
       if planet1 ∉ planets ∨ planet2 ∉ planets then
         []
       else
         let index1 := planets.idxOf planet1
         let index2 := planets.idxOf planet2
         let minIdx := if index1 < index2 then index1 else index2
         let maxIdx := if index1 < index2 then index2 else index1
         planets.filter (fun planet => minIdx < planets.idxOf planet ∧ planets.idxOf planet < maxIdx))
  constructor
  · rfl
  · split_ifs with h
    · simp
    · simp at h
      push_neg at h
      constructor
      · intro str hstr
        simp [List.mem_filter] at hstr
        exact hstr.1
      · constructor
        · intro planet hplanet
          simp [List.mem_filter]
          constructor
          · intro hmem
            exact hmem.2
          · intro hcond
            exact ⟨hplanet, hcond⟩
        · apply filter_preserves_order
          exact planets_sorted

-- #test implementation "Jupiter" "Neptune" = ["Saturn", "Uranus"]
-- #test implementation "Earth" "Mercury" = ["Venus"]
-- #test implementation "Mercury" "Uranus" = ["Venus", "Earth", "Mars", "Jupiter", "Saturn"]