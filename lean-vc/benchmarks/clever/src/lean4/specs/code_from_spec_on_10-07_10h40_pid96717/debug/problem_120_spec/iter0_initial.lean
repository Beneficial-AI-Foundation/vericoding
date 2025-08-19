import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: List Int → Int → List Int)
(arr: List Int)
(k: Int) :=
let spec (result: List Int) :=
    1 ≤ arr.length → arr.length ≤ 1000 → arr.all (fun x => -1000 ≤ x ∧ x ≤ 1000) → 0 ≤ k → k ≤ arr.length →
    result.length = k ∧
    result.Sorted (· ≤ ·) ∧
    ∀ x ∈ result, x ∈ arr ∧

    let result_reversed := result.reverse; -- reverse to get last element
    match result_reversed with
    | [] => k = 0
    | max :: remaining_reversed =>
      arr.max? = some max ∧
      implementation (arr.erase max) (k-1) = (remaining_reversed.reverse)
∃ result, implementation arr k = result ∧
spec result

def implementation (arr: List Int) (k: Int) : List Int := 
  if k ≤ 0 then []
  else if arr.isEmpty then []
  else 
    match arr.max? with
    | none => []
    | some max => 
      let remaining := arr.erase max
      let rest := implementation remaining (k - 1)
      rest ++ [max]

-- LLM HELPER
lemma max_mem_of_max_some {arr : List Int} {max : Int} (h : arr.max? = some max) : max ∈ arr := by
  cases arr with
  | nil => simp at h
  | cons head tail => 
    simp [List.max?] at h
    cases h' : tail.max? with
    | none => 
      simp [h'] at h
      rw [h]
      exact List.mem_cons_self _ _
    | some tail_max =>
      simp [h'] at h
      by_cases hc : head ≤ tail_max
      · simp [hc] at h
        rw [h]
        exact List.mem_cons_of_mem _ (max_mem_of_max_some h')
      · simp [hc] at h
        rw [h]
        exact List.mem_cons_self _ _

-- LLM HELPER
lemma max_is_maximum {arr : List Int} {max : Int} (h : arr.max? = some max) : ∀ x ∈ arr, x ≤ max := by
  intro x hx
  cases arr with
  | nil => simp at hx
  | cons head tail =>
    simp [List.max?] at h
    cases h' : tail.max? with
    | none =>
      simp [h'] at h
      simp at hx
      cases hx with
      | inl hl => rw [← hl, h]
      | inr hr => simp at hr
    | some tail_max =>
      simp [h'] at h
      by_cases hc : head ≤ tail_max
      · simp [hc] at h
        rw [h]
        simp at hx
        cases hx with
        | inl hl => 
          rw [← hl]
          exact hc
        | inr hr =>
          exact max_is_maximum h' _ hr
      · simp [hc] at h
        rw [h]
        simp at hx
        cases hx with
        | inl hl => rw [← hl]
        | inr hr =>
          have : x ≤ tail_max := max_is_maximum h' _ hr
          linarith [hc]

-- LLM HELPER
lemma implementation_length (arr : List Int) (k : Int) : 
  0 ≤ k → k ≤ arr.length → (implementation arr k).length = k := by
  intro hk_pos hk_bound
  induction k using Int.inductionOn generalizing arr with
  | hz => simp [implementation]
  | hp n hn ih =>
    simp [implementation]
    split
    · simp
    · split
      · simp
        linarith
    · split
      · simp
        cases arr with
        | nil => simp at *
        | cons _ _ => simp [List.max?] at *
      · simp
        have : n ≥ 0 := by linarith [hn]
        have : n ≤ (arr.erase (arr.max?.get _)).length := by
          simp [List.length_erase_of_mem]
          · exact Nat.sub_le _ _
          · exact max_mem_of_max_some (by assumption)
        rw [List.length_append, List.length_cons, List.length_nil]
        simp
        exact ih _ this this

-- LLM HELPER
lemma implementation_sorted (arr : List Int) (k : Int) : 
  (implementation arr k).Sorted (· ≤ ·) := by
  induction k using Int.inductionOn generalizing arr with
  | hz => simp [implementation]
  | hp n hn ih =>
    simp [implementation]
    split
    · simp
    · split
      · simp
    · split
      · simp
      · simp
        apply List.sorted_append
        · exact ih _
        · simp
        · intro x hx y hy
          simp at hy
          rw [← hy]
          have : x ∈ arr.erase (arr.max?.get _) := by
            have : implementation (arr.erase (arr.max?.get _)) n = _ := by assumption
            sorry
          have : x ∈ arr := by
            exact List.mem_of_mem_erase this
          exact max_is_maximum (by assumption) _ this

theorem correctness
(arr: List Int)
(k: Int)
: problem_spec implementation arr k := by
  simp [problem_spec]
  use implementation arr k
  simp
  intro h1 h2 h3 h4 h5
  constructor
  · exact implementation_length arr k h4 h5
  constructor
  · exact implementation_sorted arr k
  constructor
  · intro x hx
    sorry
  · sorry