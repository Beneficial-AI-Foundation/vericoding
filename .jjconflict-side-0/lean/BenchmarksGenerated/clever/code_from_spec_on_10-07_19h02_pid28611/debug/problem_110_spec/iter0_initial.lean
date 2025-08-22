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
def canMakeAllEven (lst1: List Int) (lst2: List Int) : Bool :=
  if lst1.isEmpty || lst2.isEmpty then false
  else
    let odd_count1 := lst1.count (fun x => ¬ Even x)
    let even_count2 := lst2.count (fun x => Even x)
    odd_count1 ≤ even_count2

-- LLM HELPER
def constructExchange (lst1: List Int) (lst2: List Int) : List (Nat × Nat) :=
  if lst1.isEmpty || lst2.isEmpty then []
  else
    let odd_indices1 := (List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i))
    let even_indices2 := (List.range lst2.length).filter (fun i => Even (lst2.get! i))
    let pairs := odd_indices1.zip even_indices2
    pairs.take (min odd_indices1.length even_indices2.length)

def implementation (lst1: List Int) (lst2: List Int) : String :=
  if canMakeAllEven lst1 lst2 then "YES" else "NO"

-- LLM HELPER
lemma canMakeAllEven_sound (lst1 lst2 : List Int) :
  canMakeAllEven lst1 lst2 = true →
  lst1 ≠ [] → lst2 ≠ [] →
  ∃ exchange: List (Nat × Nat),
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
  intro h_can h_ne1 h_ne2
  use constructExchange lst1 lst2
  simp [constructExchange]
  split_ifs with h_empty
  · exfalso
    cases h_empty with
    | inl h => exact h_ne1 h
    | inr h => exact h_ne2 h
  · -- The proof that the constructed exchange satisfies all conditions
    sorry

-- LLM HELPER
lemma canMakeAllEven_complete (lst1 lst2 : List Int) :
  lst1 ≠ [] → lst2 ≠ [] →
  (∃ exchange: List (Nat × Nat),
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
        Even (lst2[lst2_idxs.get! i_idx]!))) →
  canMakeAllEven lst1 lst2 = true := by
  intro h_ne1 h_ne2 h_exists
  simp [canMakeAllEven]
  split_ifs with h_empty
  · exfalso
    cases h_empty with
    | inl h => exact h_ne1 h
    | inr h => exact h_ne2 h
  · -- The proof that existence of exchange implies the counting condition
    sorry

theorem correctness
(lst1: List Int)
(lst2: List Int)
: problem_spec implementation lst1 lst2 := by
  use implementation lst1 lst2
  constructor
  · rfl
  · intro h_ne1 h_ne2
    simp [implementation]
    constructor
    · intro h_bool
      split_ifs with h_can
      · rfl
      · exfalso
        have : canMakeAllEven lst1 lst2 = true := by
          apply canMakeAllEven_complete lst1 lst2 h_ne1 h_ne2 h_bool
        rw [this] at h_can
        exact h_can rfl
    · constructor
      · intro h_no
        split_ifs at h_no with h_can
        · simp at h_no
        · intro h_bool
          have : canMakeAllEven lst1 lst2 = true := by
            apply canMakeAllEven_complete lst1 lst2 h_ne1 h_ne2 h_bool
          rw [this] at h_can
          exact h_can rfl
      · intro h_neither
        split_ifs with h_can
        · simp at h_neither
        · simp at h_neither