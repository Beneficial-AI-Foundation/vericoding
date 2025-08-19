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

-- LLM HELPER
def find_min_diff_pair (numbers: List Rat): (Rat × Rat) :=
  match numbers with
  | [] => (0, 0)
  | [x] => (x, x)
  | x :: xs =>
    let pairs := List.bind (x :: xs) (fun a => List.map (x :: xs) (fun b => if a ≤ b then (a, b) else (b, a)))
    let non_empty_pairs := List.filter pairs (fun _ => true)
    match non_empty_pairs with
    | [] => (x, x)
    | p :: ps =>
      List.foldl ps (fun acc pair =>
        let (a1, b1) := acc
        let (a2, b2) := pair
        if abs (b2 - a2) < abs (b1 - a1) then (a2, b2) else acc
      ) p

def implementation (numbers: List Rat): (Rat × Rat) := find_min_diff_pair numbers

-- LLM HELPER
lemma mem_bind_map {α β : Type*} (l : List α) (f : α → β) (g : α → List β) (x : α) (hx : x ∈ l) :
  f x ∈ List.bind l (fun a => [f a]) :=
by
  simp [List.mem_bind]
  use x
  exact ⟨hx, rfl⟩

-- LLM HELPER
lemma exists_pair_in_numbers (numbers : List Rat) (h : 2 ≤ numbers.length) :
  ∃ x y, x ∈ numbers ∧ y ∈ numbers :=
by
  cases' numbers with a as
  · simp at h
  cases' as with b bs
  · simp at h
  use a, b
  simp

-- LLM HELPER
lemma foldl_preserves_property {α : Type*} (l : List α) (init : α) (f : α → α → α) (P : α → Prop) 
  (h_init : P init) (h_f : ∀ acc x, P acc → P (f acc x)) : P (List.foldl f init l) :=
by
  induction l generalizing init with
  | nil => exact h_init
  | cons head tail ih =>
    simp [List.foldl]
    apply ih
    exact h_f init head h_init

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  use implementation numbers
  constructor
  · rfl
  · intro h_len
    unfold implementation find_min_diff_pair
    cases' numbers with a as
    · simp at h_len
    cases' as with b bs
    · simp at h_len
    simp
    have h_mem_a : a ∈ [a, b] := by simp
    have h_mem_b : b ∈ [a, b] := by simp
    constructor
    · by_cases h : a ≤ b
      · exact h
      · simp [h]
        exact le_of_not_le h
    constructor
    · by_cases h : a ≤ b
      · exact h_mem_a
      · exact h_mem_b
    constructor
    · by_cases h : a ≤ b
      · exact h_mem_b
      · exact h_mem_a
    constructor
    · intro x y hx hy
      simp at hx hy
      cases' hx with hx hx <;> cases' hy with hy hy
      · simp [hx, hy]
      · simp [hx, hy]
        by_cases h : a ≤ b
        · simp [h]
        · simp [h]
          rw [abs_sub_comm]
      · simp [hx, hy]
        by_cases h : a ≤ b
        · simp [h]
        · simp [h]
      · simp [hx, hy]
    · intro h_eq
      by_cases h : a ≤ b
      · simp [h] at h_eq
        simp [h_eq]
      · simp [h] at h_eq
        simp [h_eq]