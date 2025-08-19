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
def Even (n : Int) : Prop := ∃ k, n = 2 * k

-- LLM HELPER
def can_make_all_even (lst1: List Int) (lst2: List Int) : Bool :=
  if lst1.isEmpty || lst2.isEmpty then false
  else
    let odd_count_lst1 := lst1.length - (lst1.filter (fun x => Even x)).length
    let even_count_lst2 := (lst2.filter (fun x => Even x)).length
    odd_count_lst1 ≤ even_count_lst2

def implementation (lst1: List Int) (lst2: List Int) : String := 
  if can_make_all_even lst1 lst2 then "YES" else "NO"

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
          intro h_exists
          simp [can_make_all_even] at h
          by_cases h_empty : lst1.isEmpty ∨ lst2.isEmpty
          · cases h_empty with
            | inl h1 => 
              simp [List.isEmpty_iff_eq_nil] at h1
              rw [h1] at h_exists
              simp at h_exists
            | inr h2 =>
              simp [List.isEmpty_iff_eq_nil] at h2
              rw [h2] at h_exists
              simp at h_exists
          · simp [h_empty] at h
            cases h_exists with
            | mk exchange h_props =>
              simp at h_props
        · intro h_not_valid
          simp at h_not_valid