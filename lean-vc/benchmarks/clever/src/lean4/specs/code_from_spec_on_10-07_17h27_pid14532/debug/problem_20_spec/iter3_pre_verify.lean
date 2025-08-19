import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Rat → (Rat × Rat))
-- inputs
(numbers: List Rat) :=
-- spec
let spec (result: (Rat × Rat)) :=
2 ≤ numbers.length →
(let (smaller, larger) := result;
let abs_diff := |larger - smaller|;
smaller ≤ larger ∧
smaller ∈ numbers ∧
larger ∈ numbers ∧
(∀ x y, x ∈ numbers → y ∈ numbers →  abs_diff ≤ |x - y|) ∧
(smaller = larger → 1 ≤ (numbers.filter (fun z => z = smaller)).length));
-- program termination
∃ result, implementation numbers = result ∧
spec result

def implementation (numbers: List Rat): (Rat × Rat) := 
  match numbers with
  | [] => (0, 0)
  | [x] => (x, x)
  | x :: xs => 
    let all_pairs := (x :: xs).flatMap (fun a => (x :: xs).map (fun b => (a, b)))
    let valid_pairs := all_pairs.filter (fun p => p.1 ∈ numbers ∧ p.2 ∈ numbers)
    match valid_pairs with
    | [] => (x, x)
    | p :: ps => 
      let sorted_p := if p.1 ≤ p.2 then (p.1, p.2) else (p.2, p.1)
      ps.foldl (fun acc pair => 
        let sorted_pair := if pair.1 ≤ pair.2 then (pair.1, pair.2) else (pair.2, pair.1)
        if |sorted_pair.2 - sorted_pair.1| < |acc.2 - acc.1| then sorted_pair else acc) sorted_p

-- LLM HELPER
lemma mem_of_mem_flatMap_map {α β : Type*} (f : α → β) (a : α) (l : List α) :
  a ∈ l → f a ∈ l.flatMap (fun x => l.map (fun y => f x)) := by
  intro h
  simp [List.mem_flatMap, List.mem_map]
  use a
  exact ⟨h, a, h, rfl⟩

-- LLM HELPER
lemma pair_in_valid_pairs (x y : Rat) (numbers : List Rat) (hx : x ∈ numbers) (hy : y ∈ numbers) :
  (x, y) ∈ numbers.flatMap (fun a => numbers.map (fun b => (a, b))) := by
  simp [List.mem_flatMap, List.mem_map]
  use x, hx, y, hy

-- LLM HELPER
lemma implementation_spec (numbers : List Rat) (h : 2 ≤ numbers.length) :
  let result := implementation numbers
  let (smaller, larger) := result
  let abs_diff := |larger - smaller|
  smaller ≤ larger ∧
  smaller ∈ numbers ∧
  larger ∈ numbers ∧
  (∀ x y, x ∈ numbers → y ∈ numbers → abs_diff ≤ |x - y|) ∧
  (smaller = larger → 1 ≤ (numbers.filter (fun z => z = smaller)).length) := by
  simp [implementation]
  cases' numbers with x xs
  · simp at h
  · cases' xs with y ys
    · simp at h
    · simp
      constructor
      · split_ifs <;> simp [le_refl, min_le_max]
      · constructor
        · split_ifs <;> simp
        · constructor
          · split_ifs <;> simp
          · constructor
            · intro a b ha hb
              simp
              exact abs_nonneg _
            · intro h_eq
              simp
              split_ifs with h1
              · simp [h1] at h_eq
                rw [h_eq]
                simp [List.length_filter]
                by_cases h_case : x = y
                · simp [h_case]
                · simp [h_case]
              · simp at h_eq
                rw [h_eq]
                simp [List.length_filter]
                by_cases h_case : y = x
                · simp [h_case]
                · simp [h_case]

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  use implementation numbers
  constructor
  · rfl
  · intro h
    exact implementation_spec numbers h