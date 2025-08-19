import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(lst: List Int) :=
-- spec
let spec (result: List Int) :=
  let sorted_lst := lst.mergeSort;
  (List.Perm lst result)
  ∧ (forall i, (0 <= i ∧ i < lst.length ∧ i % 2 = 0) → result[i]! = sorted_lst[i / 2]!)
  ∧ (forall i, (0 <= i ∧ i < lst.length ∧ i % 2 = 1) → result[i]! = sorted_lst[lst.length - (i-1)/2 - 1]!)
-- program termination
∃ result, implementation lst = result ∧ spec result

-- LLM HELPER
def interleave_sorted (lst: List Int): List Int :=
  let sorted := lst.mergeSort
  let n := sorted.length
  let first_half := sorted.take ((n + 1) / 2)
  let second_half := sorted.drop ((n + 1) / 2)
  let reversed_second := second_half.reverse
  List.join (List.zipWith (fun a b => [a, b]) first_half (reversed_second ++ List.replicate first_half.length 0))
    |>.take n

def implementation (lst: List Int): List Int := 
  let sorted := lst.mergeSort
  let n := sorted.length
  if n = 0 then []
  else
    let result := List.range n |>.map (fun i =>
      if i % 2 = 0 then sorted[i / 2]!
      else sorted[n - (i - 1) / 2 - 1]!)
    result

-- LLM HELPER
lemma get_in_bounds {α : Type*} (l : List α) (i : Nat) (h : i < l.length) : 
  l[i]! = l.get ⟨i, h⟩ := by
  rw [List.getElem_eq_get]

-- LLM HELPER
lemma div_two_lt {n i : Nat} (hi : i < n) (heven : i % 2 = 0) : i / 2 < n := by
  have : i / 2 ≤ i := Nat.div_le_self i 2
  exact Nat.lt_of_le_of_lt this hi

-- LLM HELPER
lemma reverse_index_bound {n i : Nat} (hi : i < n) (hodd : i % 2 = 1) : 
  n - (i - 1) / 2 - 1 < n := by
  have h1 : (i - 1) / 2 < i := by
    rw [Nat.div_lt_iff_lt_mul_right (by norm_num : 0 < 2)]
    cases' i with i
    · contradiction
    · simp [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      exact Nat.lt_two_mul_self i
  have h2 : (i - 1) / 2 < n := Nat.lt_of_lt_of_le h1 (Nat.le_of_lt hi)
  exact Nat.sub_sub_lt_of_lt h2

-- LLM HELPER
lemma perm_mergeSort (l : List Int) : List.Perm l l.mergeSort := by
  exact List.perm_mergeSort l

theorem correctness
(lst: List Int)
: problem_spec implementation lst
:= by
  unfold problem_spec
  use implementation lst
  constructor
  · rfl
  · unfold implementation
    simp only [List.mergeSort]
    constructor
    · exact perm_mergeSort lst
    · constructor
      · intro i hi
        simp only [List.getElem_map, List.getElem_range]
        split_ifs with h
        · rfl
        · contradiction
      · intro i hi
        simp only [List.getElem_map, List.getElem_range]
        split_ifs with h
        · contradiction
        · rfl