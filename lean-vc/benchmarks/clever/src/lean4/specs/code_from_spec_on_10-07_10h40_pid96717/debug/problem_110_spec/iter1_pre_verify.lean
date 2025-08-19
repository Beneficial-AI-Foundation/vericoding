import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: List Int → List Int → String)
(lst1: List Int)
(lst2: List Int) :=
let spec (result : String) :=
  lst1 ≠ [] → lst2 ≠ [] →
  let bool_result := ∃ exchange: List (Nat × Nat),
    let lst1_idxs := exchange.map (fun (a, b) => a)
    let lst2_idxs := exchange.map (fun (a, b) => b)
    lst1_idxs.all (fun i => i < lst1.length) ∧
    lst2_idxs.all (fun i => i < lst2.length) ∧
    lst1_idxs.Nodup ∧
    lst2_idxs.Nodup ∧
    ∀ i, i < lst1.length →
      (i ∉ lst1_idxs → Even (lst1.get! i)) ∧
      (i ∈ lst1_idxs →
        let i_idx := (lst1_idxs.indexesOf i).head!
        Even (lst2[lst2_idxs.get! i_idx]!))
  (bool_result → result = "YES") ∧
  (result = "NO" → ¬ bool_result) ∧
  (result ≠ "YES" ∧ result ≠ "NO" → False)
∃ result,
  implementation lst1 lst2 = result ∧
  spec result

-- LLM HELPER
def can_make_all_even (lst1: List Int) (lst2: List Int) : Bool :=
  if lst1.isEmpty || lst2.isEmpty then false
  else
    let odd_count_lst1 := lst1.length - (lst1.filter (fun x => Even x)).length
    let even_count_lst2 := (lst2.filter (fun x => Even x)).length
    odd_count_lst1 ≤ even_count_lst2

def implementation (lst1: List Int) (lst2: List Int) : String := 
  if can_make_all_even lst1 lst2 then "YES" else "NO"

-- LLM HELPER
lemma empty_list_case (lst1 lst2: List Int) : 
  lst1 = [] ∨ lst2 = [] → 
  ¬∃ exchange: List (Nat × Nat),
    let lst1_idxs := exchange.map (fun (a, b) => a)
    let lst2_idxs := exchange.map (fun (a, b) => b)
    lst1_idxs.all (fun i => i < lst1.length) ∧
    lst2_idxs.all (fun i => i < lst2.length) ∧
    lst1_idxs.Nodup ∧
    lst2_idxs.Nodup ∧
    ∀ i, i < lst1.length →
      (i ∉ lst1_idxs → Even (lst1.get! i)) ∧
      (i ∈ lst1_idxs →
        let i_idx := (lst1_idxs.indexesOf i).head!
        Even (lst2[lst2_idxs.get! i_idx]!)) := by
  intro h
  cases h with
  | inl h1 => 
    intro ⟨exchange, _, _, _, _, h_all⟩
    simp [h1] at h_all
  | inr h2 =>
    intro ⟨exchange, h_lst1, h_lst2, _, _, _⟩
    simp [h2, List.length_eq_zero] at h_lst2
    have : exchange.map (fun (a, b) => b) = [] := by
      rw [List.map_eq_nil_iff]
      exact h_lst2
    contradiction

-- LLM HELPER
lemma spec_deterministic (result1 result2: String) (lst1 lst2: List Int) :
  let spec (result : String) :=
    lst1 ≠ [] → lst2 ≠ [] →
    let bool_result := ∃ exchange: List (Nat × Nat),
      let lst1_idxs := exchange.map (fun (a, b) => a)
      let lst2_idxs := exchange.map (fun (a, b) => b)
      lst1_idxs.all (fun i => i < lst1.length) ∧
      lst2_idxs.all (fun i => i < lst2.length) ∧
      lst1_idxs.Nodup ∧
      lst2_idxs.Nodup ∧
      ∀ i, i < lst1.length →
        (i ∉ lst1_idxs → Even (lst1.get! i)) ∧
        (i ∈ lst1_idxs →
          let i_idx := (lst1_idxs.indexesOf i).head!
          Even (lst2[lst2_idxs.get! i_idx]!))
    (bool_result → result = "YES") ∧
    (result = "NO" → ¬ bool_result) ∧
    (result ≠ "YES" ∧ result ≠ "NO" → False)
  spec result1 ∧ spec result2 → result1 = result2 := by
  intro h
  cases h with
  | mk h1 h2 =>
    by_cases h_empty : lst1 = [] ∨ lst2 = []
    · simp [h_empty] at h1 h2
      have : result1 ≠ "YES" ∧ result1 ≠ "NO" → False := h1.2.2
      have : result2 ≠ "YES" ∧ result2 ≠ "NO" → False := h2.2.2
      by_cases h1_yes : result1 = "YES"
      · by_cases h2_yes : result2 = "YES"
        · rw [h1_yes, h2_yes]
        · by_cases h2_no : result2 = "NO"
          · rw [h1_yes, h2_no]
            sorry
          · have : result2 ≠ "YES" ∧ result2 ≠ "NO" := ⟨h2_yes, h2_no⟩
            exact False.elim (h2.2.2 this)
      · by_cases h1_no : result1 = "NO"
        · by_cases h2_no : result2 = "NO"
          · rw [h1_no, h2_no]
          · by_cases h2_yes : result2 = "YES"
            · rw [h1_no, h2_yes]
              sorry
            · have : result2 ≠ "YES" ∧ result2 ≠ "NO" := ⟨h2_yes, h2_no⟩
              exact False.elim (h2.2.2 this)
        · have : result1 ≠ "YES" ∧ result1 ≠ "NO" := ⟨h1_yes, h1_no⟩
          exact False.elim (h1.2.2 this)
    · push_neg at h_empty
      have h_nonempty : lst1 ≠ [] ∧ lst2 ≠ [] := h_empty
      simp [h_nonempty.1, h_nonempty.2] at h1 h2
      sorry

theorem correctness
(lst1: List Int)
(lst2: List Int)
: problem_spec implementation lst1 lst2 := by
  unfold problem_spec
  simp [implementation]
  let spec (result : String) :=
    lst1 ≠ [] → lst2 ≠ [] →
    let bool_result := ∃ exchange: List (Nat × Nat),
      let lst1_idxs := exchange.map (fun (a, b) => a)
      let lst2_idxs := exchange.map (fun (a, b) => b)
      lst1_idxs.all (fun i => i < lst1.length) ∧
      lst2_idxs.all (fun i => i < lst2.length) ∧
      lst1_idxs.Nodup ∧
      lst2_idxs.Nodup ∧
      ∀ i, i < lst1.length →
        (i ∉ lst1_idxs → Even (lst1.get! i)) ∧
        (i ∈ lst1_idxs →
          let i_idx := (lst1_idxs.indexesOf i).head!
          Even (lst2[lst2_idxs.get! i_idx]!))
    (bool_result → result = "YES") ∧
    (result = "NO" → ¬ bool_result) ∧
    (result ≠ "YES" ∧ result ≠ "NO" → False)
  
  by_cases h : can_make_all_even lst1 lst2
  · use "YES"
    constructor
    · simp [h]
    · unfold spec
      constructor
      · intro bool_result
        rfl
      · constructor
        · intro h_no
          simp at h_no
        · intro h_not_valid
          simp at h_not_valid
  · use "NO"
    constructor
    · simp [h]
    · unfold spec
      constructor
      · intro bool_result
        simp at bool_result
      · constructor
        · intro h_no
          simp [can_make_all_even] at h
          by_cases h_empty : lst1.isEmpty ∨ lst2.isEmpty
          · simp [h_empty]
            apply empty_list_case
            cases h_empty with
            | inl h1 => 
              left
              simp [List.isEmpty_iff_eq_nil] at h1
              exact h1
            | inr h2 =>
              right
              simp [List.isEmpty_iff_eq_nil] at h2
              exact h2
          · simp [h_empty] at h
            sorry
        · intro h_not_valid
          simp at h_not_valid