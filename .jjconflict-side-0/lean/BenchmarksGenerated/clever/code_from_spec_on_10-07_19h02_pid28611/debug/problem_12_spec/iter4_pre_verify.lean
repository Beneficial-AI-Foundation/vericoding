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
      have : x ∈ xs ∨ x ∈ tail := by
        simp [List.mem_cons] at hacc
        cases hacc with
        | inl h2 => 
          right
          rw [h2]
          exact List.mem_cons_self x tail
        | inr h2 => 
          right
          exact List.mem_cons_of_mem x h2
      exact this.right
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
  sorry

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
          · intro j hj
            simp at hj