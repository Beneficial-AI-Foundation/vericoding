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
  rw [List.getElem_eq_get]

-- LLM HELPER
lemma div_two_lt {n i : Nat} (hi : i < n) (heven : i % 2 = 0) : i / 2 < n := by
  have : i / 2 ≤ i := Nat.div_le_self i 2
  exact Nat.lt_of_le_of_lt this hi

-- LLM HELPER
lemma reverse_index_bound {n i : Nat} (hi : i < n) (hodd : i % 2 = 1) : 
  n - (i - 1) / 2 - 1 < n := by
  have h1 : (i - 1) / 2 < i := by
    cases' i with i
    · contradiction
    · simp [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      have : i / 2 < i := Nat.div_lt_self (by omega) (by norm_num)
      exact Nat.lt_of_le_of_lt (Nat.div_le_div_right (Nat.le_refl i)) (Nat.lt_succ_of_le (Nat.le_refl i))
  have h2 : (i - 1) / 2 < n := Nat.lt_of_lt_of_le h1 (Nat.le_of_lt hi)
  exact Nat.sub_lt_of_pos_le _ _ (Nat.zero_lt_of_ne_zero (fun h => by
    have : n > 0 := Nat.pos_of_ne_zero (fun hn => by
      rw [hn] at hi
      exact Nat.not_lt_zero i hi)
    exact Nat.ne_of_gt this h)) (Nat.le_sub_of_add_le (Nat.add_le_of_le_sub (Nat.le_refl _) h2))

-- LLM HELPER
lemma perm_mergeSort (l : List Int) : List.Perm l l.mergeSort := by
  exact List.Perm.mergeSort l

-- LLM HELPER
lemma map_range_perm (lst : List Int) : 
  let sorted := lst.mergeSort
  let n := sorted.length
  List.Perm lst (if n = 0 then [] else List.map (fun i => if i % 2 = 0 then sorted[i / 2]! else sorted[n - (i - 1) / 2 - 1]!) (List.range n)) := by
  sorry

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
      · simp [List.mergeSort_nil_iff.mpr (List.length_eq_zero.mp h)]
        exact List.Perm.nil
      · have : lst.mergeSort.length = lst.length := List.length_mergeSort lst
        rw [h] at this
        simp [this]
        exact List.Perm.trans (perm_mergeSort lst) (List.Perm.symm (map_range_perm lst))
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