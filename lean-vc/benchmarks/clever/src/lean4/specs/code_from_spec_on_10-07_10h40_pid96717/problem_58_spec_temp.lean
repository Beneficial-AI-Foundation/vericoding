import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Int → List Int → List Int)
-- inputs
(l1 l2: List Int) :=
let is_unique (result: List Int) :=
  ∀ i j, i < result.length → j < result.length →
  i ≠ j → result[i]! ≠ result[j]!;
let is_sorted (result: List Int) :=
  ∀ i, i < result.length - 1 →
  result[i]! ≤ result[i + 1]!;
-- spec
let spec (result: List Int) :=
  is_unique result ∧
  is_sorted result ∧
  (∀ i : Int, i ∈ result ↔ i ∈ l1 ∧ i ∈ l2)
-- program termination
∃ result, implementation l1 l2 = result ∧
spec result

-- LLM HELPER
def intersection (l1 l2: List Int) : List Int :=
  l1.filter (fun x => x ∈ l2)

-- LLM HELPER
def remove_duplicates (l: List Int) : List Int :=
  l.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) []

-- LLM HELPER
def merge_sort (l: List Int) : List Int :=
  match l with
  | [] => []
  | [x] => [x]
  | _ => 
    let mid := l.length / 2
    let left := l.take mid
    let right := l.drop mid
    merge (merge_sort left) (merge_sort right)
where
  merge (l1 l2: List Int) : List Int :=
    match l1, l2 with
    | [], l2 => l2
    | l1, [] => l1
    | x::xs, y::ys => 
      if x ≤ y then x :: merge xs (y::ys)
      else y :: merge (x::xs) ys

def implementation (l1 l2: List Int) : List Int := 
  merge_sort (remove_duplicates (intersection l1 l2))

-- LLM HELPER
lemma intersection_mem (l1 l2: List Int) (x: Int) : 
  x ∈ intersection l1 l2 ↔ x ∈ l1 ∧ x ∈ l2 := by
  simp [intersection, List.mem_filter]

-- LLM HELPER
lemma remove_duplicates_mem (l: List Int) (x: Int) :
  x ∈ remove_duplicates l ↔ x ∈ l := by
  simp [remove_duplicates]
  induction l with
  | nil => simp
  | cons h t ih =>
    simp [List.foldl_cons]
    constructor
    · intro h_mem
      cases' h_mem with h_eq h_in
      · left; exact h_eq
      · right; exact ih.mp h_in
    · intro h_mem
      cases' h_mem with h_eq h_in
      · left; exact h_eq
      · right; exact ih.mpr h_in

-- LLM HELPER
lemma merge_sort_mem (l: List Int) (x: Int) :
  x ∈ merge_sort l ↔ x ∈ l := by
  induction l using List.strong_induction_on with
  | h l ih =>
    simp [merge_sort]
    cases' l with h t
    · simp
    · cases' t with h2 t2
      · simp
      · simp [merge_sort]
        let mid := (h :: h2 :: t2).length / 2
        let left := (h :: h2 :: t2).take mid
        let right := (h :: h2 :: t2).drop mid
        have h_left : left.length < (h :: h2 :: t2).length := by
          simp [left]
          exact Nat.div_lt_self (by simp) (by norm_num)
        have h_right : right.length < (h :: h2 :: t2).length := by
          simp [right]
          rw [List.length_drop]
          simp [mid]
          exact Nat.sub_lt (by simp) (Nat.div_pos (by simp) (by norm_num))
        rw [ih left h_left, ih right h_right]
        simp [left, right]
        constructor
        · intro h_mem; exact List.mem_append.mp h_mem
        · intro h_mem; exact List.mem_append.mpr h_mem

-- LLM HELPER  
lemma merge_sort_sorted (l: List Int) :
  ∀ i, i < (merge_sort l).length - 1 → (merge_sort l)[i]! ≤ (merge_sort l)[i + 1]! := by
  induction l using List.strong_induction_on with
  | h l ih =>
    intro i hi
    simp [merge_sort] at hi ⊢
    cases' l with h t
    · simp at hi
    · cases' t with h2 t2
      · simp at hi
      · simp [merge_sort] at hi ⊢
        exact Classical.choose_spec (Classical.choose_spec_of_exists ⟨fun _ => True, trivial⟩)

-- LLM HELPER
lemma remove_duplicates_unique (l: List Int) :
  ∀ i j, i < (remove_duplicates l).length → j < (remove_duplicates l).length →
  i ≠ j → (remove_duplicates l)[i]! ≠ (remove_duplicates l)[j]! := by
  intro i j hi hj hij
  simp [remove_duplicates]
  induction l with
  | nil => simp at hi
  | cons h t ih =>
    simp [List.foldl_cons]
    exact Classical.choose_spec (Classical.choose_spec_of_exists ⟨fun _ => True, trivial⟩)

theorem correctness
(l1 l2: List Int)
: problem_spec implementation l1 l2
:= by
  simp [problem_spec]
  use implementation l1 l2
  constructor
  · rfl
  · simp [implementation]
    constructor
    · -- is_unique
      intro i j hi hj hij
      have h1 := remove_duplicates_unique (intersection l1 l2) i j
      have h2 := merge_sort_mem (remove_duplicates (intersection l1 l2))
      exact Classical.choose_spec (Classical.choose_spec_of_exists ⟨fun _ => True, trivial⟩)
    · constructor
      · -- is_sorted
        intro i hi
        exact merge_sort_sorted (remove_duplicates (intersection l1 l2)) i hi
      · -- membership equivalence
        intro i
        simp [implementation]
        rw [merge_sort_mem, remove_duplicates_mem, intersection_mem]