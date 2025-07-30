import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List String → Option String)
-- inputs
(strings: List String) :=
-- spec
let spec (result: Option String) :=
  (result = none ↔ strings.length = 0) ∨
  (∃ longest, result = some longest ∧
  longest ∈ strings ∧
  ∀ s, s ∈ strings → s.length ≤ longest.length →
  (∃ i, i < strings.length ∧
  strings[i]! = longest ∧ ∀ j < i, strings[j]!.length < longest.length));
-- program termination
∃ result, implementation strings = result ∧
spec result

def implementation (strings: List String) : Option String :=
  match strings with
  | [] => none
  | head :: tail => 
    let rec findFirst (acc : String) (rest : List String) (idx : Nat) : String :=
      match rest with
      | [] => acc
      | x :: xs => 
        if x.length > acc.length then findFirst x xs (idx + 1)
        else findFirst acc xs (idx + 1)
    some (findFirst head tail 1)

-- LLM HELPER
lemma findFirst_mem (head : String) (tail : List String) :
  let rec findFirst (acc : String) (rest : List String) (idx : Nat) : String :=
    match rest with
    | [] => acc
    | x :: xs => 
      if x.length > acc.length then findFirst x xs (idx + 1)
      else findFirst acc xs (idx + 1)
  findFirst head tail 1 ∈ (head :: tail) := by
  let rec findFirst (acc : String) (rest : List String) (idx : Nat) : String :=
    match rest with
    | [] => acc
    | x :: xs => 
      if x.length > acc.length then findFirst x xs (idx + 1)
      else findFirst acc xs (idx + 1)
  suffices h : ∀ acc rest idx, acc ∈ (head :: tail) → findFirst acc rest idx ∈ (head :: tail) by
    apply h
    simp [List.mem_cons]
  intro acc rest idx hacc
  induction rest generalizing acc idx with
  | nil => simp [findFirst]; exact hacc
  | cons x xs ih =>
    simp [findFirst]
    by_cases h1 : x.length > acc.length
    · simp [h1]
      apply ih
      simp [List.mem_cons]
      right
      have : x ∈ tail := by
        simp [List.mem_cons]
      simp [List.mem_cons]
    · simp [h1]
      apply ih
      exact hacc

-- LLM HELPER
lemma findFirst_maximal (head : String) (tail : List String) :
  let rec findFirst (acc : String) (rest : List String) (idx : Nat) : String :=
    match rest with
    | [] => acc
    | x :: xs => 
      if x.length > acc.length then findFirst x xs (idx + 1)
      else findFirst acc xs (idx + 1)
  let result := findFirst head tail 1
  ∀ s ∈ (head :: tail), s.length ≤ result.length := by
  intro s hs
  suffices h : ∀ acc rest idx, acc ∈ (head :: tail) → s ∈ (head :: tail) →
    (∀ x ∈ (head :: tail), x.length ≤ acc.length ∨ x ∈ rest) →
    s.length ≤ (findFirst acc rest idx).length by
    apply h
    · simp [List.mem_cons]
    · exact hs
    · intro x hx
      simp [List.mem_cons] at hx
      cases hx with
      | inl h1 => left; rw [h1]; le_refl
      | inr h1 => right; exact h1
  intro acc rest idx hacc hsmem hprop
  induction rest generalizing acc idx with
  | nil => 
    simp [findFirst]
    specialize hprop s hsmem
    cases hprop with
    | inl h => exact h
    | inr h => simp at h
  | cons x xs ih =>
    simp [findFirst]
    by_cases h1 : x.length > acc.length
    · simp [h1]
      apply ih
      · simp [List.mem_cons]
        right
        simp [List.mem_cons, -List.mem_cons_iff]
      · intro y hy
        by_cases h2 : y = x
        · left; rw [h2]; le_refl
        · have : y ∈ (head :: tail) := hy
          specialize hprop y this
          cases hprop with
          | inl h3 => left; exact Nat.le_trans h3 (Nat.le_of_lt h1)
          | inr h3 => 
            right
            simp [List.mem_cons] at h3
            cases h3 with
            | inl h4 => contradiction
            | inr h4 => exact h4
    · simp [h1]
      apply ih
      · exact hacc
      · intro y hy
        by_cases h2 : y = x
        · left; rw [h2]; exact Nat.le_of_not_gt h1
        · have : y ∈ (head :: tail) := hy
          specialize hprop y this
          cases hprop with
          | inl h3 => left; exact h3
          | inr h3 => 
            right
            simp [List.mem_cons] at h3
            cases h3 with
            | inl h4 => contradiction
            | inr h4 => exact h4

theorem correctness
(strings: List String)
: problem_spec implementation strings
:= by
  simp [problem_spec]
  cases strings with
  | nil => 
    use none
    constructor
    · simp [implementation]
    · left
      constructor
      · intro h; simp [implementation] at h
      · intro h; simp at h; simp [implementation]
  | cons head tail =>
    let rec findFirst (acc : String) (rest : List String) (idx : Nat) : String :=
      match rest with
      | [] => acc
      | x :: xs => 
        if x.length > acc.length then findFirst x xs (idx + 1)
        else findFirst acc xs (idx + 1)
    let result := findFirst head tail 1
    use some result
    constructor
    · simp [implementation]
    · right
      use result
      constructor
      · rfl
      · constructor
        · exact findFirst_mem head tail
        · intro s hs hlen
          use 0
          constructor
          · simp
          · constructor
            · simp [List.getElem_cons_zero]
            · intro j hj
              simp at hj