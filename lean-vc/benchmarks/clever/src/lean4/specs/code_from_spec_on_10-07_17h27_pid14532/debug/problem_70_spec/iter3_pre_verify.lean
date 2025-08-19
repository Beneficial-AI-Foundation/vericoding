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
  List.flatten (List.zipWith (fun a b => [a, b]) first_half (reversed_second ++ List.replicate first_half.length 0))
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
lemma get_in_bounds [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) : 
  l[i]! = l.get ⟨i, h⟩ := by
  rw [List.getElem_getElem]

-- LLM HELPER
lemma div_two_lt {n i : Nat} (hi : i < n) (heven : i % 2 = 0) : i / 2 < n := by
  have : i / 2 ≤ i := Nat.div_le_self i 2
  exact Nat.lt_of_le_of_lt this hi

-- LLM HELPER
lemma reverse_index_bound {n i : Nat} (hi : i < n) (hodd : i % 2 = 1) : 
  n - (i - 1) / 2 - 1 < n := by
  have h1 : (i - 1) / 2 < n := by
    have : (i - 1) / 2 ≤ (i - 1) := Nat.div_le_self (i - 1) 2
    have : (i - 1) < n := by
      cases' i with i
      · simp at hodd
      · simp [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
        exact Nat.lt_of_succ_lt_succ hi
    exact Nat.lt_of_le_of_lt this ‹(i - 1) < n›
  have h2 : n > 0 := Nat.pos_of_ne_zero (fun hn => by
    rw [hn] at hi
    exact Nat.not_lt_zero i hi)
  have h3 : (i - 1) / 2 + 1 ≤ n := Nat.succ_le_of_lt h1
  exact Nat.sub_lt h2 (Nat.zero_lt_succ _)

-- LLM HELPER
lemma perm_mergeSort (l : List Int) : List.Perm l l.mergeSort := 
  List.Perm.mergeSort l

-- LLM HELPER
lemma map_range_perm (lst : List Int) : 
  let sorted := lst.mergeSort
  let n := sorted.length
  List.Perm lst (if n = 0 then [] else List.map (fun i => if i % 2 = 0 then sorted[i / 2]! else sorted[n - (i - 1) / 2 - 1]!) (List.range n)) := by
  let sorted := lst.mergeSort
  let n := sorted.length
  have h_perm : List.Perm lst sorted := List.Perm.mergeSort lst
  have h_len : sorted.length = lst.length := List.length_mergeSort lst
  rw [h_len]
  if h : lst.length = 0 then
    simp [h]
    rw [List.length_eq_zero.mp h]
    exact List.Perm.nil
  else
    have : n = lst.length := by rw [← h_len]
    rw [← this]
    exact List.Perm.trans h_perm (List.Perm.refl _)

theorem correctness
(lst: List Int)
: problem_spec implementation lst
:= by
  unfold problem_spec
  use implementation lst
  constructor
  · rfl
  · unfold implementation
    constructor
    · cases' h : lst.length with n
      · simp [List.length_eq_zero.mp h]
        exact List.Perm.nil
      · have : lst.mergeSort.length = lst.length := List.length_mergeSort lst
        rw [h] at this
        simp [this]
        exact List.Perm.trans (perm_mergeSort lst) (List.Perm.refl _)
    · constructor
      · intro i hi
        simp only [and_imp] at hi
        obtain ⟨hi_nonneg, hi_lt, hi_even⟩ := hi
        simp [implementation]
        have : lst.mergeSort.length = lst.length := List.length_mergeSort lst
        rw [← this] at hi_lt
        cases' h : lst.mergeSort.length with n
        · simp [h] at hi_lt
        · simp [h, List.getElem_map, List.getElem_range, hi_even]
      · intro i hi
        simp only [and_imp] at hi
        obtain ⟨hi_nonneg, hi_lt, hi_odd⟩ := hi
        simp [implementation]
        have : lst.mergeSort.length = lst.length := List.length_mergeSort lst
        rw [← this] at hi_lt
        cases' h : lst.mergeSort.length with n
        · simp [h] at hi_lt
        · simp [h, List.getElem_map, List.getElem_range, hi_odd]